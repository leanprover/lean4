import Lean.Elab.Command

variable (P : Bool → Prop)
variable (o : Option Nat)

/-!
This test checks that `simp [foo]` where `foo` is `reducible` uses the unfolding machinery,
not the equations machinery.
-/

@[reducible] def red : Option α → Bool
  | .some _ => true
  | .none => false

-- check that simp rewrites even without constants

/--
error: tactic 'fail' failed
P : Bool → Prop
o : Option Nat
⊢ P
    (match o with
    | some val => true
    | none => false)
-/
#guard_msgs in
theorem ex1 : P (red o) := by simp [red]; fail

-- check that the equational theorems have not been generated

/-- info: false -/
#guard_msgs in
run_meta Lean.logInfo m!"{← Lean.hasConst `red.eq_1}"

-- Again, the same for the `simp` attribute

attribute [simp] red

/-- info: false -/
#guard_msgs in
run_meta Lean.logInfo m!"{← Lean.hasConst `red.eq_1}"

/--
error: tactic 'fail' failed
P : Bool → Prop
o : Option Nat
⊢ P
    (match o with
    | some val => true
    | none => false)
-/
#guard_msgs in
theorem ex1' : P (red o) := by simp; fail

-- For comparison, the behavior for a semi-reducible function

def semired : Option α → Bool
  | .some _ => true
  | .none => false

-- At least for now, non-recursive functions are also unfolded by simp (as per
-- `SimpTheorems.unfoldEvenWithEqns`), in addition to applying their rewrite rules:

/--
error: tactic 'fail' failed
P : Bool → Prop
o : Option Nat
⊢ P
    (match o with
    | some val => true
    | none => false)
-/
#guard_msgs in
theorem ex2 : P (semired o) := by simp [semired]; fail

-- check that the equational theorems have been generated

/-- info: true -/
#guard_msgs in
run_meta Lean.logInfo m!"{← Lean.hasConst `semired.eq_1}"

def semired2 : Option α → Bool
  | .some _ => true
  | .none => false

attribute [simp] semired2

/-- info: true -/
#guard_msgs in
run_meta Lean.logInfo m!"{← Lean.hasConst `semired2.eq_1}"

/--
error: tactic 'fail' failed
P : Bool → Prop
o : Option Nat
⊢ P
    (match o with
    | some val => true
    | none => false)
-/
#guard_msgs in
theorem ex2' : P (semired2 o) := by simp; fail
