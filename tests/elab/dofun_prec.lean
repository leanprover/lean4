

def tst1 (x : Nat) : IO Unit := do
if x > 0 then
  IO.println "hello"
  IO.println "world"

def tst2 (xs : List Nat) : IO Unit :=
xs.forM fun x => do
  IO.println x
