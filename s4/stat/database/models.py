from flask_sqlalchemy import SQLAlchemy


__all__ = [
	"db",
	"Voter",
	"Color_Submission",
	"Survey_Submission",
]

db = SQLAlchemy()


# ================================================== #
# models / query functions 							 #
# ================================================== #
class Voter(db.Model):
	__tablename__ =         "voters"

	id =					db.Column("id",		        db.Integer, primary_key=True)
	survey_first =          db.Column("survey_first",   db.Boolean)

	def __init__(self, survey_first: bool) -> None:
		self.survey_first = survey_first


class Color_Submission(db.Model):
	__tablename__ =         "color_submissions"

	id =   				    db.Column("id",	            db.Integer, primary_key=True)
	voter_id =              db.Column("voter_id",       db.Integer)
	color_a =               db.Column("color_a",        db.String(10))
	color_b =               db.Column("color_b",        db.String(10))
	chose_a =               db.Column("chose_a",        db.Boolean)

	def __init__(self, voter_id: int, color_a: str, color_b: str, chose_a: bool) -> None:
		self.voter_id = voter_id
		self.color_a = color_a
		self.color_b = color_b
		self.chose_a = chose_a

	@property
	def voter(self) -> Voter:
		return query_voters(id=self.voter_id)


class Survey_Submission(db.Model):
	__tablename__ =         "survey_submissions"

	id =   				    db.Column("id",	            db.Integer, primary_key=True)
	voter_id =              db.Column("voter_id",       db.Integer)
	age =                   db.Column("age",            db.Integer)
	male =                  db.Column("male",           db.Boolean)
	student =               db.Column("student",        db.Boolean)
	name =                  db.Column("name",           db.String(127))
	city =                  db.Column("city",           db.String(127))
	street =                db.Column("street",         db.String(127))
	zip =                   db.Column("zip",            db.String(16))

	def __init__(self, voter_id: int, name: str, age: int, male: bool, student: bool, city: str, street: str, zip: str) -> None:
		self.voter_id = voter_id
		self.name = name
		self.age = age
		self.male = male
		self.student = student
		self.city = city
		self.street = street
		self.zip = zip

	@property
	def voter(self) -> Voter:
		return query_voters(id=self.voter_id)


def query_voters(**kwargs):             return Voter.query.filter_by(**kwargs)
def query_color_submissions(**kwargs):  return Color_Submission.query.filter_by(**kwargs)
def query_survey_submissions(**kwargs): return Survey_Submission.query.filter_by(**kwargs)