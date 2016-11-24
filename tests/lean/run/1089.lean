import init.string
import init.bool
import system.io

inductive token
| eof : token
| plus : token
| var : string -> token

open token
open option

def to_token : string → option token
| [] := none
| (c :: cs) :=
  let t : option token := match c with
    | #"x" := some (var "x")
    | #"y" := some (var "y")
    | #"+" := some plus
    | _ := none
  end in t
