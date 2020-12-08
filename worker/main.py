import logging
import json
import requests
import tempfile
import base64
import os
import contextlib
import subprocess
import time
import re
import functools
import filelock
import itertools
import sys
from requests_toolbelt import sessions
from requests.exceptions import RetryError
from requests.adapters import HTTPAdapter
from requests.packages.urllib3.util.retry import Retry
from worker.parser.SMTLIBv2Transform import *
from worker.parser.SMTLIBv2Parser import *
from worker.parser.SMTLIBv2Lexer import *

import config

class TimeoutHTTPAdapter(HTTPAdapter):
    def __init__(self, *args, **kwargs):
        self.timeout = 5 # seconds
        if "timeout" in kwargs:
            self.timeout = kwargs['timeout']
            del kwargs['timeout']
        super().__init__(*args, **kwargs)

    def send(self, request, **kwargs):
        timeout = kwargs.get('timeout')
        if timeout is None:
            kwargs['timeout'] = self.timeout
        return super().send(request, **kwargs)

#
# Aux functions for instance handling
def getSMTLibData(inputFile,stream=FileStream):
    lexer = SMTLIBv2Lexer(stream(inputFile)) 
    parser = SMTLIBv2Parser(CommonTokenStream(lexer))
    return SMTLIBv2Transform().getListInstance(parser.start())

def removeCommandsFromSMTLibData(smt_data,removables=[]):
    return SMTLIBv2Transform().filterDeclarations(smt_data,removables)

def smtLibDataToString(smt_data):
    return SMTLIBv2Transform().flattenData(smt_data)

def getInitalInstance(inputFile):
    return smtLibDataToString(removeCommandsFromSMTLibData(getSMTLibData(inputFile),["set-info","get-model"]))

def getAssertedModelInstance(inputFile,model_str):
    smt_data = removeCommandsFromSMTLibData(getSMTLibData(inputFile),["define-fun","declare-fun","declare-const","get-model","set-info"])
    return smtLibDataToString(SMTLIBv2Transform().insertCommands(smt_data,getSMTLibData(model_str,InputStream),1))

# This method should return a dictionary of the following form:
# {'instance_id': instance_id, 'result': string, "sat"/"unsat"/"timeout"/"unknown"/"error", 'stdout': string, runtime: integer, runtime *in milliseconds*}
def run_solver(solver_binary_path, instance_id, instance_path, arguments, timeout=20):
    logging.info(f"Running {solver_binary_path} on instance {instance_path}: {arguments}, timeout={timeout}")
    result_obj = {'instance_id': instance_id, 'node_name': config.SMTLAB_NODE_NAME}
    time = Timer ()

    timeout_ms = int(timeout * 1000.0)
    
    with tempfile.TemporaryDirectory() as tmpdirname:
        smt_instance = os.path.join (tmpdirname, "instance.smt")
        f=open(smt_instance,"w")
        f.write(getInitalInstance(instance_path))
        f.close()

        try:
            argument_array = json.loads(arguments)
            out = subprocess.check_output ([solver_binary_path] + argument_array + [smt_instance],timeout=timeout).decode('UTF-8').strip()
        except subprocess.TimeoutExpired:
            time.stop()
            result_obj['result'] = "timeout"
            result_obj['stdout'] = ""
            result_obj['runtime'] = timeout_ms
            logging.info(f"timeout, result is {result_obj}")
            return result_obj
        except subprocess.CalledProcessError as e:
            time.stop()
            result_obj['result'] = "error"
            result_obj['stdout'] = f"stdout: {e.stdout} stderr: {e.stderr}"
            result_obj['runtime'] = time.getTime_ms()
            logging.info(f"process exited with an error, result is {result_obj}")
            return result_obj
            
        time.stop()    

        result_obj['stdout'] = out
        result_obj['runtime'] = time.getTime_ms()

        if "unsat" in out:
            result_obj['result'] = "unsat"
        elif "sat" in out:
            result_obj['result'] = "sat"
        elif time.getTime() >= timeout:
            # sometimes python's subprocess does not terminate eagerly  
            result_obj['result'] = "timeout"
            result_obj['runtime'] = timeout_ms
        elif "unknown" in out:
            result_obj['result'] = "unknown"
        else:
            result_obj['result'] = "error"
            

        logging.info(f"result is {result_obj}")
    return result_obj    

def validate_result(solver_binary_path, solver_arguments, instance_path, model):
    result_obj = {}
    result_obj['validation'] = "error"
    result_obj['stdout'] = ""

    # create new smt instance
    with tempfile.TemporaryDirectory() as tmpdirname:
        validation_file = os.path.join (tmpdirname, "validation.smt")
        f=open(validation_file,"w")
        f.write(getAssertedModelInstance(instance_path,model))
        f.close()

        # perform validation - pass a "fake" instance ID since we don't need it
        veri_result_obj = run_solver(solver_binary_path, 0, validation_file, solver_arguments)
        result_obj['stdout'] = veri_result_obj['stdout']
        if veri_result_obj['result'] == "sat":
            result_obj['validation'] = "valid"
            logging.info(f"successfully verified.")
        elif veri_result_obj['result'] == "unsat":
            result_obj['validation'] = "invalid"
            logging.info(f"found an invalid model.")
        else:
            result_obj['validation'] = veri_result_obj['result']
            logging.info(f"validation inconclusive.")

        return result_obj

   
class Worker():
    def __init__(self, solvers):
        logging.basicConfig(level=config.LOG_LEVEL)
        self.solvers = solvers
        self.http = sessions.BaseUrlSession(base_url=config.SMTLAB_API_ENDPOINT)
        retry_strategy = Retry(total=5, method_whitelist=["HEAD", "GET", "PUT", "POST", "OPTIONS"], status_forcelist=[429, 500, 502, 503, 504], backoff_factor=1)
        adapter = TimeoutHTTPAdapter(max_retries = retry_strategy)
        self.http.mount("http://", adapter)
        self.http.mount("https://", adapter)
        self.http.auth = (config.SMTLAB_USERNAME, config.SMTLAB_PASSWORD)
        assert_status_hook = lambda response, *args, **kwargs: response.raise_for_status()
        self.http.hooks['response'] = [assert_status_hook]
        
    def get_solver_path_or_download(self, solver_id):
        key = f"smtlab-solver-{solver_id}.bin"
        keypath = config.SMTLAB_SOLVER_DIR + "/" + key
        lockpath = keypath + ".lock"
        if os.path.exists(keypath):
            return keypath
        else:
            # download the solver to SMTLAB_SOLVER_DIR, mark it as executable, and rename it to 'keypath'
            lock = filelock.FileLock(lockpath)
            with lock:
                # test again - the file may have just been created if there was contention on this lock
                if os.path.exists(keypath):
                    return keypath
                else:
                    solver_path = ""
                    logging.info(f"Downloading solver {solver_id}.")
                    with tempfile.NamedTemporaryFile(mode="w+b", dir=config.SMTLAB_SOLVER_DIR, delete=False) as fp_solver:
                        r = self.http.get(f"solvers/{solver_id}")
                        fp_solver.write(base64.b64decode(r.json()['base64_binary']))
                        fp_solver.flush()
                        fp_solver.close()
                        solver_path = fp_solver.name
                    os.rename(solver_path, keypath)
                    os.chmod(keypath, 0o500)
                    return keypath                
        
    def run(self):
        logging.info("Starting SMTLab worker")
        if not os.path.exists(config.SMTLAB_SOLVER_DIR):
            try:
                os.makedirs(config.SMTLAB_SOLVER_DIR)
            except FileExistsError:
                pass
        for queue in config.QUEUES:
            logging.info(f"Will check {queue} queue")
        backoff = 0
        while True:
            try:
                got_message = False
                for queue in config.QUEUES:
                    r = self.http.get(f"queues/{queue}")
                    messages = r.json()
                    if len(messages) > 0:
                        got_message = True
                        for message in messages:
                            try:
                                payload = json.loads(message)
                                self.handle_message(payload)
                            except json.JSONDecodeError:
                                logging.error(f"Received invalid message {message}")
                if got_message:
                    backoff = 0
                else:
                    time.sleep(0.1 * 2.0 ** backoff)
                    if backoff < config.QUEUE_BACKOFF_LIMIT:
                        print(f"No messages, backing off (n={backoff})")
                        backoff += 1
            except RetryError as e:
                logging.error(f"Cancelled request due to maximum retry limit being reached -- check API server status: {e}")

    def handle_message(self, payload):
        logging.info(f"Received message {payload}")
        
        if "action" not in payload:
            logging.error("received message with no 'action'")
            return
        if payload['action'] == "run":
            # run instances
            if "run_id" not in payload or "solver_id" not in payload or "instance_id" not in payload or "arguments" not in payload:
                logging.error("received 'run' message with missing required fields")
                return
            instance_id = payload['instance_id']
            logging.info(f"Running instance {instance_id} with solver {payload['solver_id']}")
            # download the solver binary to a temporary directory
            # TODO cache this across multiple messages
            fp_solver = self.get_solver_path_or_download(payload['solver_id'])
            # download all instances
            with tempfile.NamedTemporaryFile(mode="w+", suffix=".smt2") as fp_instance:
                logging.info(f"Downloading instance {instance_id}.")
                r = self.http.get(f"instances/{instance_id}")
                fp_instance.write(r.json()['body'])
                fp_instance.flush()
                result = run_solver(fp_solver, instance_id, fp_instance.name, payload['arguments'])
                result_action = {'action': 'process_results', 'run_id': payload['run_id'], 'results': [result]}
                self.http.post("queues/scheduler", json=result_action)
        elif payload['action'] == "validate":
            # validate a result
            if "result_id" not in payload or "solver_id" not in payload:
                logging.error("received 'validate' message with missing required fields")
                return
            logging.info(f"Validating result {payload['result_id']} with solver {payload['solver_id']}")
            fp_solver = self.get_solver_path_or_download(payload['solver_id'])
            solver_arguments = None
            for solver in self.solvers:
                if solver['id'] == payload['solver_id']:
                    solver_arguments = solver['default_arguments']
                    break
            if solver_arguments is None:
                # update cached solver data
                r = self.http.get("solvers")
                self.solvers = r.json()
                solver_arguments = "[]"
                for solver in self.solvers:
                    if solver['id'] == payload['solver_id']:
                        solver_arguments = solver['default_arguments']
                        break
            # fetch the result data...
            r_result = self.http.get(f"results/{payload['result_id']}")
            result_info = r_result.json()

            # we are only able to verfiy sat instances with a model 
            # TODO: move this to another place later
            if result_info['result'] != "sat":
                logging.info(f"received 'validate' message for result {payload['result_id']} which is not reported as satisfiable.")
                return

            smt_model = "".join(result_info['stdout'].split("\n")[1:-1])[len("(model"):] # strip output "sat" and the surrounding (model ...); works for CVC4 and Z3 models

            # ...and download the correct instance
            # TODO cache these as well
            with tempfile.NamedTemporaryFile(mode="w+", suffix=".smt2") as fp_instance:
                r = self.http.get(f"instances/{result_info['instance_id']}")
                fp_instance.write(r.json()['body'])
                fp_instance.flush()
                result = validate_result(fp_solver, solver_arguments, fp_instance.name, smt_model)
                result_action = {'action': 'process_validation', 'result_id': payload['result_id'], 'solver_id': payload['solver_id'], 'validation': result['validation'], 'stdout': result['stdout']}
                self.http.post("queues/scheduler", json=result_action)
        else:
            logging.error(f"received message with unknown 'action' {payload['action']}")

class Timer:
    def __init__(self):
        self._l1 = time.perf_counter()

    def stop (self):
        self._l2 = time.perf_counter ()

    def getTime (self):
        return self._l2-self._l1

    def getTime_ms(self):
        return int(self.getTime() * 1000.0)
