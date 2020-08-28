import os
import logging

LOG_LEVEL = logging.INFO
SMTLAB_API_ENDPOINT = os.environ.get('SMTLAB_API_ENDPOINT') or 'http://127.0.0.1:5000'
QUEUE_URL = os.environ.get('SMTLAB_QUEUE_URL') or 'http://127.0.0.1:9324'
QUEUES = ['regression', 'performance']
try:
    THREADS = int(os.environ.get('SMTLAB_WORKER_THREADS')) or 1
except ValueError:
    logging.warn("SMTLAB_WORKER_THREADS environment variable must be an integer")
    THREADS = 1
