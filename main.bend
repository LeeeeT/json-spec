import Base
import ./json/LAWS.bend as JSON
import ./json/PROOF.bend as JSONProof

# Reads the answer of a users API from stdin, e.g.
#   [{"name": "Ann", "age": 31, "admin": true, "email": "ann@example.com"},
#    {"name": "Bob", "age": 27, "admin": false, "email": null}]
# and prints one line per user, then the admins.

# Reading values

def email.pick(s: Maybe<String>) -> String:
  match s:
    case Some{x}:
      x
    case None{}:
      "no email"

# A user, as a line of the report.
def user(+u: JSON.JSON) -> Maybe<String>:
  do Maybe<String>:
    name_j : JSON.JSON <- JSON.field(u, "name")
    name : String <- JSON.string(name_j)
    age_j : JSON.JSON <- JSON.field(u, "age")
    age : String <- JSON.number(age_j)
    email_j : JSON.JSON <- JSON.field(u, "email")
    return name ++ ", " ++ age ++ ", " ++ email.pick(JSON.string(email_j))

# The name of a user who is an admin.
def admin.if(name: String, admin: Bool) -> Maybe<String>:
  match admin:
    case True{}:
      Some{name}
    case False{}:
      None{}

def admin(+u: JSON.JSON) -> Maybe<String>:
  do Maybe<String>:
    name_j : JSON.JSON <- JSON.field(u, "name")
    name : String <- JSON.string(name_j)
    admin_j : JSON.JSON <- JSON.field(u, "admin")
    is_admin : Bool <- JSON.bool(admin_j)
    admin.if(name, is_admin)

# Output

def line(m: Maybe<String>) -> String:
  match m:
    case Some{s}:
      s ++ "\n"
    case None{}:
      "(malformed user)\n"

def lines(us: +List<JSON.JSON>) -> String:
  match us:
    case Nil{}:
      ""
    case u <> rest:
      line(user(u)) ++ lines(rest)

def name(m: Maybe<String>) -> String:
  match m:
    case Some{s}:
      s ++ " "
    case None{}:
      ""

def admins(us: +List<JSON.JSON>) -> String:
  match us:
    case Nil{}:
      ""
    case u <> rest:
      name(admin(u)) ++ admins(rest)

def report(+users: +List<JSON.JSON>) -> String:
  lines(users) ++ "admins: " ++ admins(users) ++ "\n"

def analyze.users(users: Maybe<+List<JSON.JSON>>) -> String:
  match users:
    case Some{us}:
      report(us)
    case None{}:
      "expected an array of users\n"

def analyze(j: Maybe<JSON.JSON>) -> String:
  match j:
    case Some{v}:
      analyze.users(JSON.array(v))
    case None{}:
      "not JSON\n"

def finish(read: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (input, result) = read
  do IO<Unit>:
    File.close(input)
    text : String <- IO.pass(String, result)
    IO.write(analyze(JSON.load(text)))

def main() -> IO(Unit):
  do IO<Unit>:
    input : File <- IO.try(File, File.open("/dev/stdin", "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(input, 1048576)
    finish(read)
