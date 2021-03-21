open Lean

def f : Name → Name
| n@(`foo.bla) => n
| _ => Name.anonymous

def tst : IO Unit := do
if hash `foo.bla != hash (f `foo.bla) then
  throw $ IO.userError "bug"
IO.println "ok"

#eval tst
