import Base
import ./json/LAWS.bend as JSON
import ./json/PROOF.bend as JSONProof

def report(valid: Bool) -> IO(Unit):
  match valid:
    case True{}:
      IO.print("Valid JSON")
    case False{}:
      IO.print("Not JSON")

def finish(read: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (input, result) = read
  do IO<Unit>:
    File.close(input)
    text : String <- IO.pass(String, result)
    report(JSON.check(text))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.write("Enter JSON: ")
    input : File <- IO.try(File, File.open("/dev/stdin", "r"))
    read : File & Result<&1, &1, U32 & String, String> <- File.read(input, 1048576)
    finish(read)
