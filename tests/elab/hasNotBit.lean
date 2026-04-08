import Lean

open Lean Meta

/-!
Testing Elab and Kernel reduction behavior with regards to Nat.shiftRight.
-/

example : [x].ctorIdx = 1 := rfl

example : Nat.land 1 (Nat.shiftRight 8 1) = 0 := rfl

-- The WHNF reduction does not reduce here:

/--
error: Type mismatch
  Eq.refl 0
has type
  0 = 0
but is expected to have type
  Nat.land 1 (Nat.shiftRight 8 [x].ctorIdx) = 0
-/
#guard_msgs in
example : Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx)) = 0 := Eq.refl 0

example : Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx)) = 0 :=
  @id (Nat.land 1 (Nat.shiftRight 8 1) = 0) (Eq.refl 0)

elab "refl0" : tactic =>
  Lean.Elab.Tactic.closeMainGoalUsing `refl0 fun _ _ =>
    Lean.Meta.mkEqRefl (Lean.mkRawNatLit 0)

example : Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx)) = 0 := by
  refl0


elab "eagerrefl0" : tactic =>
  Lean.Elab.Tactic.closeMainGoalUsing `refl0 fun _ _ => do
    Lean.Meta.mkAppM `eagerReduce #[← Lean.Meta.mkEqRefl (Lean.mkRawNatLit 0)]

example : Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx)) = 0 := by
  eagerrefl0

-- A variant that uses the expected (unreduced) type as the first argument to eagerReduce
elab "eagerrefl0'" : tactic =>
  Lean.Elab.Tactic.closeMainGoalUsing `refl0 fun goal _ => do
    let u ← getLevel goal
    return mkApp2 (mkConst ``eagerReduce [u]) goal (← mkEqRefl (mkRawNatLit 0))

example : Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx)) = 0 := by
  eagerrefl0'

/--
error: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  (Nat.land 1 (Nat.shiftRight 8 [x].ctorIdx)).beq 0 = true
in the application
  Nat.eq_of_beq_eq_true (Eq.refl true)
-/
#guard_msgs in
example : Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx)) = 0 :=
  Nat.eq_of_beq_eq_true (Eq.refl true)

/--
error: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  (Nat.land 1 (Nat.shiftRight 8 [x].ctorIdx)).beq 0 = true
in the application
  eagerReduce (Eq.refl true)
-/
#guard_msgs in
example : Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx)) = 0 :=
  Nat.eq_of_beq_eq_true (eagerReduce (Eq.refl true))

elab "reflTrue" : tactic =>
  Lean.Elab.Tactic.closeMainGoalUsing `refl0 fun _ _ =>
    Lean.Meta.mkEqRefl (Lean.mkConst ``Bool.true)

-- This works! (But why?)
example : Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx)) = 0 :=
  Nat.eq_of_beq_eq_true (by reflTrue)


/--
error: Type mismatch
  Eq.refl true
has type
  true = true
but is expected to have type
  (Nat.land 1 (Nat.shiftRight 8 [x].ctorIdx)).beq 0 = true
-/
#guard_msgs in
example : Nat.beq (Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx))) 0 := Eq.refl true

-- This also works (But why?)
example : Nat.beq (Nat.land 1 (Nat.shiftRight 8 ([x].ctorIdx))) 0 := by reflTrue
