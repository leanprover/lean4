/--
error: Dependent elimination failed: Type mismatch when solving this alternative: it has type
  motive false
but is expected to have type
  motive b✝
-/
#guard_msgs in
def test1 b := match b with
  | .(false) => 1
  | true => 2

/--
error: Dependent elimination failed: Type mismatch when solving this alternative: it has type
  motive false ⋯
but is expected to have type
  motive x✝¹ x✝
-/
#guard_msgs in
def test2 : (b : Bool) → (h : b = false) → Nat
  | .(false), .(rfl) => 1
  | true, _ => 2

-- works
def test3 : (b : Bool) → (h : b = false) → Nat
  | .(false), rfl => 1

/--
@ +3:4...11
error: Redundant alternative: Any expression matching
  true, x✝
will match one of the preceding alternatives
-/
#guard_msgs (positions := true) in
def test4 : (b : Bool) → (h : b = false) → Nat
  | .(false), rfl => 1
  | true, _ => 2 -- error here
