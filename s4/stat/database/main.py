import random

from flask import Flask, request, jsonify, make_response
from flask_cors import CORS

from socket import socket, AF_INET, SOCK_DGRAM
import sys
import os

from models import *


# ================================================== #
# global variables / functions						 #
# ================================================== #
server = Flask(
	__name__,
	template_folder=None,
	static_folder=None
)
CORS(server, resources=r'/api/*')

server.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False
server.config["SQLALCHEMY_DATABASE_URI"] = rf"sqlite:///{os.path.dirname(__file__)}/db/servey.sqlite3"


# ================================================== #
# global variables / functions						 #
# ================================================== #
def start_server(host_ip: str, port: int = 80, debug: bool = False) -> None:
	db.init_app(server)
	with server.app_context():
		db.create_all()

	server.run(host=host_ip, port=port, debug=debug)


# ================================================== #
# global variables / functions						 #
# ================================================== #
@server.route("/api/start", methods=["GET"])
def start_call():
	voter = Voter(random.randint(0, 1) == 1)
	db.session.add(voter)
	db.session.commit()

	return make_response(
		jsonify(
			id=             voter.id,
			survey_first=   voter.survey_first
		),
		200  # success code
	)


@server.route("/api/submit_color", methods=["POST"])
def submit_color_call():
	submission = Color_Submission(
		request.json["id"],
		request.json["color_a"],
		request.json["color_b"],
		request.json["chose_a"]
	)
	db.session.add(submission)
	db.session.commit()

	return make_response(
		jsonify(success=True),
		200  # success code
	)


@server.route("/api/submit_survey", methods=["POST"])
def submit_survey_call():
	submission = Survey_Submission(
		request.json["id"],
		request.json["age"],
		request.json["male"],
		request.json["student"],
		request.json["occupation"]
	)
	db.session.add(submission)
	db.session.commit()

	return make_response(
		jsonify(success=True),
		200  # success code
	)


# ================================================== #
# global variables / functions						 #
# ================================================== #
if __name__ == "__main__":  # run server only
	args = sys.argv[1:]

	os.system("cls" if os.name in ["nt", "dos"] else "clear")
	if "-help" in args: print(
		"[-offline]\t\t-> run server on (127.0.0.1:80) instead of local ipv4",
		"[-debug]\t\t-> run server in debug mode",
		"[-quiet]\t\t-> run server without logging to the terminal",
		sep="\n", end="\n\n"
	)

	port = 80
	host_ip = "127.0.0.1"
	if "-offline" not in args:
		sock = socket(AF_INET, SOCK_DGRAM)
		sock.connect(("8.8.8.8", 9699))
		host_ip = sock.getsockname()[0]
		sock.close()
	if "-quiet" in args:
		import logging
		logging.getLogger('werkzeug').disabled = True
		server.logger.disabled = True
		print(f"\nserver: http://{host_ip}:{port}\n")

	start_server(host_ip, port, "-debug" in args)
