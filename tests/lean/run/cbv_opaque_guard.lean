set_option cbv.warning false

/-! Test that `@[cbv_opaque]` is respected by `reduceRecMatcher` and `reduceProj`. -/

/-! `@[cbv_opaque]` constants are not unfolded. -/

@[cbv_opaque] def secret : Nat := 42

/--
error: unsolved goals
⊢ secret = 42
-/
#guard_msgs in
example : secret = 42 := by conv => lhs; cbv

/-! Equation theorems fire but `@[cbv_opaque]` arguments stay intact. -/

def addOne (n : Nat) : Nat := n + 1

/--
error: unsolved goals
⊢ secret.succ = 43
-/
#guard_msgs in
example : addOne secret = 43 := by conv => lhs; cbv

/-! Pattern matching on a `@[cbv_opaque]` discriminant gets stuck. -/

def isZero (n : Nat) : Bool :=
  match n with
  | 0 => true
  | _ + 1 => false

/--
error: unsolved goals
⊢ (match secret with
    | 0 => true
    | n.succ => false) =
    false
-/
#guard_msgs in
example : isZero secret = false := by conv => lhs; cbv

/-! Recursive functions with `@[cbv_opaque]` arguments get stuck at the match. -/

def myLength : List Nat → Nat
  | [] => 0
  | _ :: xs => 1 + myLength xs

@[cbv_opaque] def secretList : List Nat := [1, 2, 3]

/--
error: unsolved goals
⊢ (match secretList with
    | [] => 0
    | head :: xs => 1 + myLength xs) =
    3
-/
#guard_msgs in
example : myLength secretList = 3 := by conv => lhs; cbv

/-! Projections on `@[cbv_opaque]` structures are not reduced. -/

@[cbv_opaque] def secretPair : Nat × Nat := (10, 20)

/--
error: unsolved goals
⊢ secretPair.1 = 10
-/
#guard_msgs in
example : secretPair.1 = 10 := by conv => lhs; cbv

/--
error: unsolved goals
⊢ secretPair.2 = 20
-/
#guard_msgs in
example : secretPair.2 = 20 := by conv => lhs; cbv

/-! Non `@[cbv_opaque]` values still reduce normally. -/

def normalVal : Nat := 42

example : normalVal + 1 = 43 := by cbv
example : isZero normalVal = false := by cbv

def normalPair : Nat × Nat := (10, 20)

example : normalPair.1 = 10 := by cbv
example : normalPair.2 = 20 := by cbv

/-! The kernel's `isDefEq` in `cbvGoalCore` still closes `@[cbv_opaque]` goals. -/

example : secret = 42 := by cbv
example : secretPair.1 = 10 := by cbv
