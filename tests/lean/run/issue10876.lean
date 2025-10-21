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
