from . import main

def run_worker():
    worker = main.Worker()
    worker.run()
