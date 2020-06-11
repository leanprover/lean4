new_frontend

def tst1 (x : Nat) : IO Unit :=
when (x > 0) do
  IO.println "hello";
  IO.println "world"

def tst2 (xs : List Nat) : IO Unit :=
xs.forM fun x => do
  IO.println x
