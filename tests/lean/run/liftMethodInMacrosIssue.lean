
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

/-- info: x is 0 -/
#guard_msgs in
#eval tst 0

/-- info: x is 1 -/
#guard_msgs in
#eval tst 1

/-- info: other -/
#guard_msgs in
#eval tst 2

syntax term "<|||>" term : doElem

macro_rules
| `(doElem| $a:term <|||> $b) => `(doElem| if (← $a) then pure true else $b:term)

def tst2 : IO Bool := do
pure true <|||> (← throw $ IO.userError "failed")

/-- info: true -/
#guard_msgs in
#eval tst2
