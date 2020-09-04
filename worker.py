#!/usr/bin/env python

import config
import worker
import multiprocessing

if __name__ == '__main__':
    multiprocessing.set_start_method("spawn")
    processes = []
    for i in range(config.THREADS):
        proc = multiprocessing.Process(target=worker.run_worker, args=())
        processes.append(proc)
        proc.start()
    try:
        while True:
            pass
    except KeyboardInterrupt:
        for proc in processes:
            proc.kill()
