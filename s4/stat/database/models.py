from flask_sqlalchemy import SQLAlchemy


__all__ = [
	"db",
	"Submission",
	"query_submissions"
]

db = SQLAlchemy()


# ================================================== #
# models / query functions 							 #
# ================================================== #
class Submission(db.Model):
	__tablename__ =	"servey"

	_id =					db.Column("id",		db.Integer, primary_key=True)
	# mac?          (unique)
	# timestamp?
	# ip?
	value =		    		db.Column("value",	db.Integer)

	def __init__(self, value: int) -> None:
		self.value = value


def query_submissions(**kwargs): return Submission.query.filter_by(**kwargs)
