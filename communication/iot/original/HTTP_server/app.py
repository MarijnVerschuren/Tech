from flask import Flask
from socket import *
import sys

app = Flask(__name__)


@app.route("/", methods=["GET", "POST", "PUT", "DELETE", "HEAD"])
def hello_world():  # put application's code here
    return bytes([i for i in range(0, 256)])


if __name__ == "__main__":
    args = sys.argv[1:]
    start_args = []
    if "-help" in args: print(
        "[-offline]\t\t-> run server on (127.0.0.1:80) instead of local ipv4",
        "[-debug]\t\t-> run server in debug mode",
        "[-quiet]\t\t-> run server without logging to the terminal",
        sep="\n", end="\n\n"
    )
    if "-offline" in args: start_args.extend(["127.0.0.1", 5000])
    else: start_args.extend([gethostbyname(gethostname()), 5000])
    if "-quiet" in args:
        import logging
        logging.getLogger('werkzeug').disabled = True
        app.logger.disabled = True
        print(f"http://{start_args[0]}:{start_args[1]}")
    app.run(*start_args, debug="-debug" in args)
