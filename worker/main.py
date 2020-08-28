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
