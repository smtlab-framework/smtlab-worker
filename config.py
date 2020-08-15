import os
import logging

LOG_LEVEL = logging.DEBUG
SMTLAB_API_ENDPOINT = os.environ.get('SMTLAB_API_ENDPOINT') or 'http://127.0.0.1:5000'
QUEUE_CONNECTION = [(os.environ.get('QUEUE_HOST') or '127.0.0.1', os.environ.get('QUEUE_PORT') or 62613)]
QUEUE_USERNAME = os.environ.get('QUEUE_USER') or 'smtlab'
QUEUE_PASSWORD = os.environ.get('QUEUE_PASS') or 'smtlab'
QUEUES = ['regression', 'performance']
THREADS = os.environ.get('SMTLAB_WORKER_THREADS') or 1
