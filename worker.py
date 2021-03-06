#!/usr/bin/env python

import config
import worker
import multiprocessing
import requests

if __name__ == '__main__':
    print(f"Starting node {config.SMTLAB_NODE_NAME}")
    
    r = requests.get(config.SMTLAB_API_ENDPOINT + "/solvers", auth=(config.SMTLAB_USERNAME, config.SMTLAB_PASSWORD))
    r.raise_for_status()
    solvers = r.json()
    
    multiprocessing.set_start_method("spawn")
    processes = []
    for i in range(config.THREADS):
        proc = multiprocessing.Process(target=worker.run_worker, args=(solvers,))
        processes.append(proc)
        proc.start()
    try:
        for proc in processes:
            proc.join()
    except KeyboardInterrupt:
        for proc in processes:
            proc.kill()
