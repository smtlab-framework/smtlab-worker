import logging
import stomp
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
        out = subprocess.check_output ([solver_binary_path]+arguments+[smtfile],timeout=timeout).decode().strip()
    except subprocess.TimeoutExpired:
        time.stop()
        result_obj['result'] = "timeout"
        result_obj['stdout'] = ""
        result_obj['runtime'] = timeout_ms
        return result_obj
    except subprocess.CalledProcessError as e:
        time.stop()
        result_obj['result'] = "error"
        result_obj['stdout'] = "error-message: " + str(e) + "\nsolver-output: " + out
        result_obj['runtime'] = time.getTime_ms()
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

    logging.info(f"result is {result_obj}")
    return result_obj

class EventQueueListener(stomp.ConnectionListener):
    def __init__(self, conn):
        self.conn = conn

    def on_error(self, frame):
        logging.error(f"message queue error: {frame.body}")

    def on_message(self, frame):
        try:
            payload = json.loads(frame.body)
        except ValueError:
            logging.error(f"received malformed message: {frame.body}")
            self.conn.ack(frame.headers['message-id'], frame.headers['subscription'])
        try:
            self.handle_message(payload)
        except:
            logging.exception("Exception thrown in handle_message()")
        self.conn.ack(frame.headers['message-id'], frame.headers['subscription'])

    def handle_message(self, payload):
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
            with tempfile.NamedTemporaryFile() as fp_solver:
                r = requests.get(config.SMTLAB_API_ENDPOINT + "/solvers/{}".format(payload['solver_id']))
                r.raise_for_status()
                fp_solver.write(base64.b64decode(r.json['base64_binary']))
                fp_solver.flush()
                # make the solver binary executable
                os.chmod(fp_solver.name, 700)
                # download all instances
                with contextlib.ExitStack() as stack:
                    fp_instances = [stack.enter_context(tempfile.NamedTemporaryFile(suffix=".smt2")) for i in payload['instance_ids']]
                    # TODO this could likely be parallelized
                    for (instance_id, fp_instance) in zip(payload['instance_ids'], fp_instances):
                        r = requests.get(config.SMTLAB_API_ENDPOINT + "/instances/{}".format(instance_id))
                        r.raise_for_status()
                        fp_instance.write(r.json['body'])
                        fp_instance.flush()
                    instance_filenames = [x.name for x in fp_instances]
                    with ThreadPool(config.THREADS) as pool:
                        results = pool.map(lambda idata: run_solver(fp_solver.name, idata[0], idata[1], payload['arguments']), zip(payload['instance_ids'], instance_filenames))
                        result_action = {'action': 'process_results', 'run_id': payload['run_id'], 'results': results}
                        self.conn.send(body=json.dumps(result_action), destination="queue/scheduler")
        else:
            logging.error(f"received message with unknown 'action' {payload['action']}")

class Worker():
    def __init__(self):
        logging.basicConfig(level=config.LOG_LEVEL)
        self.conn = stomp.Connection(config.QUEUE_CONNECTION)
        self.conn.set_listener('', EventQueueListener(self.conn))

    def run(self):
        logging.info("Starting SMTLab worker")
        self.conn.connect(config.QUEUE_USERNAME, config.QUEUE_PASSWORD, wait=True)
        logging.info("Connected to queue endpoint")
        subscription_id = 1
        for queue in config.QUEUES:
            self.conn.subscribe(destination=f"queue/{queue}", id=subscription_id, ack='client-individual')
            logging.info(f"Subscribed to {queue} queue")
            subscription_id += 1
        try:
            while True:
                pass
        except KeyboardInterrupt:
            logging.info("Caught signal, shutting down")
            self.conn.disconnect()

class Timer:
    def __init__(self):
        self._l1 = time.perf_counter()

    def stop (self):
        self._l2 = time.perf_counter ()

    def getTime (self):
        return self._l2-self._l1

    def getTime_ms(self):
        return int(self.getTime() * 1000.0)
