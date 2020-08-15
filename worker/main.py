import logging
import stomp
import json
import requests
from multiprocessing.pool import ThreadPool
import tempfile
import base64
import os
import contextlib

import config

# This method should return a dictionary of the following form:
# {'instance_id': instance_id, 'result': string, "sat"/"unsat"/"timeout"/"unknown"/"error", 'stdout': string, runtime: integer, runtime *in milliseconds*}
def run_solver(solver_binary_path, instance_id, instance_path, arguments, timeout=20):
    result_obj = {'instance_id': instance_id}
    # TODO
    result_obj['result'] = "error"
    result_obj['stdout'] = "worker process not implemented yet!"
    result_obj['runtime'] = 0
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
                os.chmod(fp_solver.name, 0700)
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
                        # upload result
                        r = requests.post(config.SMTLAB_API_ENDPOINT + "/runs/{}/results".format(payload['run_id']), json=results)
                        r.raise_for_status()
                        
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
