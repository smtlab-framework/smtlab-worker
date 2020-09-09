from . import main

def run_worker(solvers):
    worker = main.Worker(solvers)
    worker.run()
