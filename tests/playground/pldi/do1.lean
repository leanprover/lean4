

def getVal : IO Nat :=
IO.rand 0 100

-- set_option trace.Elab.definition true

def g (i : Nat) : StateT Nat IO Nat := do
s ← get;
a ← getVal;   -- automatic lift being used
IO.println a;
pure (s+a)

#eval (g 10).run' 1

def h (x : Nat) : IO Nat := do
IO.println x;
pure (x+1)

def tst1 : IO Unit := do
let x := ← h $ (← getVal) + (← getVal);
/-
Syntax sugar for
  aux1 ← getVal;
  aux2 ← getVal;
  aux3 ← h aux1 aux2;
  let x := aux3;
-/
IO.println x

#eval tst1

def tst2 : IO Unit := do
if (← h 1) > 0 then
  IO.println "gt"
else
  IO.println "le"

#eval tst2
