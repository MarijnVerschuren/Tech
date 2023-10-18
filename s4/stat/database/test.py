import random

from flask import Flask, request, jsonify, make_response

import sys
import os

from models import *
from info_gen import *


server = Flask(
	__name__,
	template_folder=None,
	static_folder=None
)
server.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False
server.config["SQLALCHEMY_DATABASE_URI"] = rf"sqlite:///{os.path.dirname(__file__)}/db/servey.sqlite3"
gen = info_gen(16, 29)


if __name__ == "__main__":
	db.init_app(server)
	with server.app_context():
		db.create_all()

		count = 48
		before = 25
		data = [gen.next() for _ in range(count)]
		print(data)
		for person in data:
			sf = random.randint(0, 1)
			voter = Voter(
				bool(sf) if before else False
			)
			before -= sf
			db.session.add(voter)
			db.session.commit()

			submission = Survey_Submission(
				voter.id,
				person.name,
				person.age,
				person.gender == "male",
				random.randint(0, 100) > 15,
				person.city,
				person.street,
				person.zip_code
			)
			db.session.add(submission)
			db.session.commit()
