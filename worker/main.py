import logging
import boto3
import json
import requests
from multiprocessing.pool import ThreadPool
import tempfile
import base64
import os
import contextlib
import subprocess
import time
import re
import shutil

import config

# This method should return a dictionary of the following form:
# {'instance_id': instance_id, 'result': string, "sat"/"unsat"/"timeout"/"unknown"/"error", 'stdout': string, runtime: integer, runtime *in milliseconds*}
def run_solver(solver_binary_path, instance_id, instance_path, arguments, timeout=20):
    logging.info(f"Running {solver_binary_path} on instance {instance_path}: {arguments}, timeout={timeout}")
    result_obj = {'instance_id': instance_id}
    time = Timer ()

    timeout_ms = int(timeout * 1000.0)
    
    try:
        argument_array = json.loads(arguments)
        out = subprocess.check_output ([solver_binary_path] + argument_array + [instance_path],timeout=timeout).decode('UTF-8').strip()
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

#
# Auxiliaries for the validation
def _translate_smt26_escape_to_smt25(self,text):
    return re.sub('u{(..)}', r'x\1', re.sub('u{(.)}', r'x0\1', text))  

def _get_stripped_smt_commands(filepath,removables=["(define-fun","(declare-fun","(declare-const","(get-model"]):
    s=open(filepath,"r")
    # remove all comments
    tmp_instance = ""
    for l in s:
        if not l.startswith(";"):
            tmp_instance+=l

    # identify matching positions
    toret = dict()
    pstack = []
    for i, c in enumerate(tmp_instance):
        if c == '(':
            pstack.append(i)
        elif c == ')':
            if len(pstack) == 0:
                raise IndexError("No matching closing parens at: " + str(i))
            toret[pstack.pop()] = i
    if len(pstack) > 0:
        raise IndexError("No matching opening parens at: " + str(pstack.pop()))

    # extract matching blocks
    instance_list = []
    logic = "(set-logic ALL)"
    for (i,j) in toret.items():
        covered = False
        for (x,y) in [(n,m) for (n,m) in toret.items() if (n,m) != (i,j)]:
            this_range = list(range(x,y+1))
            if i in this_range and j in this_range:
                covered = True
                break
        if not covered:
            smt_cmd = tmp_instance[i:j+1]
            if smt_cmd.startswith("(set-logic"):
                logic=smt_cmd
            elif functools.reduce(lambda a,b : a and b, [not smt_cmd.startswith(x) for x in removables]):
                instance_list+=[tmp_instance[i:j+1]]
    return [logic]+instance_list

def validate_result(solver_binary_path, solver_arguments, instance_path, model, old_smt25_escape_translation=True):
    result_obj['validation'] = "error"
    result_obj['stdout'] = ""

    # translate \u{XX} escape sequences to the old ones (\xXX)
    if old_smt25_escape_translation:
        model=self._translate_smt26_escape_to_smt25(model)

    # create new smt instance
    new_smt_cmds = self._get_stripped_smt_commands_and_logic(instance_path)
    tmpdir = tempfile.mkdtemp ()
    validation_file = os.path.join (tmpdir,"out.smt")
    f=open(validation_file,"w")
    for l in [new_smt_cmds[0]]+[model]+new_smt_cmds[1:]:
        f.write(l+"\n")
    f.close()

    # perform validation; run solver needs an instance ID, is this needed here too?
    veri_result_obj = self.run_solver(solver_binary_path, 0, validation_file, solver_arguments)
    if veri_result_obj['result'] == "sat":
        result_obj['validation'] = "true"
        logging.info(f"successfully verified.")
    else:
        logging.info(f"found an invalid model.")

    # clean up
    shutil.rmtree (tmpdir)
    return result_obj

class Worker():
    def __init__(self):
        logging.basicConfig(level=config.LOG_LEVEL)
        self.client = boto3.resource('sqs', endpoint_url=config.QUEUE_URL, region_name='elasticmq', aws_access_key_id='x', aws_secret_access_key='x', use_ssl=False)

    def run(self):
        logging.info("Starting SMTLab worker")
        queues = []
        for queue in config.QUEUES:
            queues.append(self.client.get_queue_by_name(QueueName=queue))
            logging.info(f"Will check {queue} queue")
        try:
            while True:
                for queue in queues:
                    for message in queue.receive_messages(MaxNumberOfMessages=1, WaitTimeSeconds=1, VisibilityTimeout=60):
                        self.handle_message(message)
                        message.delete()
        except KeyboardInterrupt:
            logging.info("Caught signal, shutting down")

    def handle_message(self, message):
        logging.info(f"Received message {message.body}")
        try:
            payload = json.loads(message.body)
        except ValueError:
            logging.error(f"received malformed message: {body}")
            return
        
        if "action" not in payload:
            logging.error("received message with no 'action'")
            return
        if payload['action'] == "run":
            # run instances
            if "run_id" not in payload or "solver_id" not in payload or "instance_ids" not in payload or "arguments" not in payload:
                logging.error("received 'run' message with missing required fields")
                return
            logging.info(f"Running {len(payload['instance_ids'])} instances with solver {payload['solver_id']}")
            # download the solver binary to a temporary directory
            # TODO cache this across multiple messages
            fp_solver = tempfile.NamedTemporaryFile(mode="w+b", delete=False)
            try:
                logging.info(f"Downloading solver binary.")
                r = requests.get(config.SMTLAB_API_ENDPOINT + "/solvers/{}".format(payload['solver_id']))
                r.raise_for_status()
                fp_solver.write(base64.b64decode(r.json()['base64_binary']))
                fp_solver.flush()
                fp_solver.close()
                # make the solver binary executable
                os.chmod(fp_solver.name, 0o700)
                # extend timeout on redelivering this message to twice the maximum timeout of all runs
                message.change_visibility(VisibilityTimeout=60 + 2 * 20 * len(payload['instance_ids']))
                # download all instances
                with contextlib.ExitStack() as stack:
                    fp_instances = [stack.enter_context(tempfile.NamedTemporaryFile(mode="w+", suffix=".smt2")) for i in payload['instance_ids']]
                    # TODO this could likely be parallelized
                    for (instance_id, fp_instance) in zip(payload['instance_ids'], fp_instances):
                        logging.info(f"Downloading instance {instance_id}.")
                        r = requests.get(config.SMTLAB_API_ENDPOINT + "/instances/{}".format(instance_id))
                        r.raise_for_status()
                        fp_instance.write(r.json()['body'])
                        fp_instance.flush()
                    instance_filenames = [x.name for x in fp_instances]
                    with ThreadPool(config.THREADS) as pool:
                        results = pool.map(lambda idata: run_solver(fp_solver.name, idata[0], idata[1], payload['arguments']), zip(payload['instance_ids'], instance_filenames))
                        result_action = {'action': 'process_results', 'run_id': payload['run_id'], 'results': results}
                        queue = self.client.get_queue_by_name(QueueName="scheduler")
                        queue.send_message(MessageBody=json.dumps(result_action))
            finally:
                os.remove(fp_solver.name)
        elif payload['action'] == "validate":
            # validate a result
            if "result_id" not in payload or "solver_id" not in payload:
                logging.error("received 'validate' message with missing required fields")
                return
            logging.info(f"Validating result {payload['result_id']} with solver {payload['solver_id']}")
            # download the solver binary to a temporary directory
            # TODO cache this across multiple messages
            fp_solver = tempfile.NamedTemporaryFile(mode="w+b", delete=False)
            try:
                logging.info("Downloading solver binary.")
                r = requests.get(config.SMTLAB_API_ENDPOINT + "/solvers/{}".format(payload['solver_id']))
                r.raise_for_status()
                solver_arguments = r.json()['default_arguments']
                fp_solver.write(base64.b64decode(r.json()['base64_binary']))
                fp_solver.flush()
                fp_solver.close()
                # make binary executable
                os.chmod(fp_solver.name, 0o700)
                # extend message timeout by a few seconds
                message_change_visibility(VisibilityTimeout = 120)
                # fetch the result data...
                r_result = requests.get(config.SMTLAB_API_ENDPOINT + "/results/{}".format(payload['result_id']))
                r_result.raise_for_status()
                result_info = r_result.json()

                # we are only able to verfiy sat instances with a model 
                # TODO: move this to another place later
                if result_info['result'] != "sat":
                    logging.info(f"received 'validate' message for result {payload['result_id']} which is not reported as satisfiable.")
                    return

                smt_model = "".join(model.split("\n")[1:-1])[len("(model"):] # strip output "sat" and the surrounding (model ...); works for CVC4 and Z3 models

                # ...and download the correct instance
                # TODO cache these as well
                with tempfile.NamedTemporaryFile(mode="w+", suffix=".smt2") as fp_instance:
                    r = requests.get(config.SMTLAB_API_ENDPOINT + "/instances/{}".format(result_info['instance_id']))
                    r.raise_for_status()
                    fp_instance.write(r.json()['body'])
                    fp_instance.flush()
                    # TODO threading
                    result = validate_result(fp_solver.name, solver_arguments, fp_instance.name, smt_model)
                    result_action = {'action': 'process_validation', 'result_id': payload['result_id'], 'solver_id': payload['solver_id'], 'validation': result['validation'], 'stdout': result['stdout']}
                    queue = self.client.get_queue_by_name(QueueName="scheduler")
                    queue.send_message(MessageBody=json.dumps(result_action))
            finally:
                os.remove(fp_solver.name)
            # TODO
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
