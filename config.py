import os
import logging

LOG_LEVEL = logging.INFO
SMTLAB_API_ENDPOINT = os.environ.get('SMTLAB_API_ENDPOINT') or 'http://127.0.0.1:5000'
QUEUES = ['performance', 'regression']
QUEUE_BACKOFF_LIMIT = 8
try:
    THREADS = int(os.environ.get('SMTLAB_WORKER_THREADS') or 1)
except ValueError:
    logging.warn("SMTLAB_WORKER_THREADS environment variable must be an integer")
    THREADS = 1
SMTLAB_SOLVER_DIR = os.environ.get('SMTLAB_SOLVER_DIR') or os.getcwd() + "/solvers"
SMTLAB_USERNAME = os.environ.get('SMTLAB_USERNAME')
SMTLAB_PASSWORD = os.environ.get('SMTLAB_PASSWORD')
