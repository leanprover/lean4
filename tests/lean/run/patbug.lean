open Lean

def f : Name → Name
| n@(`foo.bla) => n
| _ => Name.anonymous

def tst : IO Unit := do
when (hash `foo.bla != hash (f `foo.bla)) $
  throw $ IO.userError "bug";
IO.println "ok"

#eval tst
