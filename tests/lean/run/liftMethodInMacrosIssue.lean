
def foo (x : Nat) : IO Bool := do
if x == 0 then
  throw $ IO.userError "foo: unexpected zero"
pure (x == 1)

def tst (x : Nat) : IO Unit := do
if x == 0 then
  IO.println "x is 0"
else if (← foo x) then
  IO.println "x is 1"
else
  IO.println "other"

#eval tst 0
#eval tst 1
#eval tst 2

syntax term "<|||>" term : doElem

macro_rules
| `(doElem| $a:term <|||> $b:term) => `(doElem| if (← $a:term) then pure true else $b:term)

def tst2 : IO Bool := do
pure true <|||> (← throw $ IO.userError "failed")

#eval tst2
