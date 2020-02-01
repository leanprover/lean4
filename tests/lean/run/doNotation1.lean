new_frontend

def f : IO Nat :=
pure 0

def g (x : Nat) : IO Nat :=
pure (x + 1)

set_option trace.Elab.definition true

def tst1 : IO Unit := do
a ← f;
let x := a + 1;
IO.println "hello";
IO.println x

def tst2 : IO Unit := do
let x := (^g $ (^f) + (^f));
IO.println "hello";
IO.println x

def tst3 : IO Unit := do
if (^g 1) > 0 then
  IO.println "gt"
else do
  x ← f;
  y ← g x;
  IO.println y
