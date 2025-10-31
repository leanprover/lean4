inductive HasUnitParam where
  | yes : Unit → HasUnitParam
  | no  : HasUnitParam

def foo (x : HasUnitParam) : Bool := x.casesOn (fun _ => true) false
def bar (x : HasUnitParam) : Bool := match x with
  | HasUnitParam.yes _x => true
  | HasUnitParam.no => false

-- Checks that the delaboration of `casesOn` does not confuse genuine unit fields with
-- the thunking parameter of a genuine matcher

/--
info: def foo : HasUnitParam → Bool :=
fun x =>
  match x with
  | HasUnitParam.yes x => true
  | HasUnitParam.no => false
-/
#guard_msgs in
#print foo

/--
info: def bar : HasUnitParam → Bool :=
fun x =>
  match x with
  | HasUnitParam.yes _x => true
  | HasUnitParam.no => false
-/
#guard_msgs in
#print bar

-- Does `split` work?

-- set_option trace.split.debug true

/--
trace: case h_1
t✝ : Bool
⊢ false = false

case h_2
t✝ : Bool
⊢ true = true
-/
#guard_msgs in
theorem splitTest (b : Bool) : b = b.casesOn false true := by
  split
  trace_state
  · rfl
  · rfl

-- #print splitTest
