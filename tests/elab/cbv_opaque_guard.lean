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

/-! `@[cbv_eval]` can override `@[cbv_opaque]`. -/

@[cbv_opaque] def opaqueAdd (a b : Nat) : Nat := a + b
@[cbv_eval] theorem opaqueAdd_eq (a b : Nat) : opaqueAdd a b = a + b := rfl

example : opaqueAdd 1 2 = 3 := by conv => lhs; cbv

/-! `@[cbv_eval]` works on bare constants (no arguments). -/

def bareConst : Nat := 2 + 3
@[cbv_eval] theorem bareConst_eq : bareConst = 5 := rfl

example : bareConst = 5 := by conv => lhs; cbv

/-! The kernel's `isDefEq` in `cbvGoalCore` still closes `@[cbv_opaque]` goals. -/

example : secret = 42 := by cbv
example : secretPair.1 = 10 := by cbv

/-! ## Interaction of `@[cbv_opaque]` and `@[cbv_eval]` -/

/-! `@[cbv_eval]` on an opaque bare constant rewrites it. -/

@[cbv_opaque] def opaqueConst : Nat := 99
@[cbv_eval] theorem opaqueConst_eq : opaqueConst = 99 := rfl

example : opaqueConst = 99 := by conv => lhs; cbv

/-! `@[cbv_eval]` on an opaque function fires and the result is further reduced. -/

@[cbv_opaque] def opaqueMul (a b : Nat) : Nat := a * b
@[cbv_eval] theorem opaqueMul_eq (a b : Nat) : opaqueMul a b = a * b := rfl

example : opaqueMul 3 4 + 1 = 13 := by conv => lhs; cbv

/-! Without `@[cbv_eval]`, an opaque constant stays stuck (cbv_opaque alone blocks). -/

@[cbv_opaque] def pureOpaque : Nat := 7

/--
error: unsolved goals
⊢ pureOpaque = 7
-/
#guard_msgs in
example : pureOpaque = 7 := by conv => lhs; cbv

/-! `@[cbv_eval ←]` (inverted) also works with `@[cbv_opaque]`. -/

@[cbv_opaque] def opaqueAlias : Nat := 42
@[cbv_eval ←] theorem opaqueAlias_eq : 42 = opaqueAlias := rfl

example : opaqueAlias = 42 := by conv => lhs; cbv

/-! `@[cbv_opaque]` with `@[cbv_eval]` still prevents unfolding of the definition itself. -/

@[cbv_opaque] def opaquePartial (n : Nat) : Nat := n * n
-- Only provide a rule for the specific case n=5
@[cbv_eval] theorem opaquePartial_5 : opaquePartial 5 = 25 := rfl

example : opaquePartial 5 = 25 := by conv => lhs; cbv

-- No rule for n=3, so it stays stuck
/--
error: unsolved goals
⊢ opaquePartial 3 = 9
-/
#guard_msgs in
example : opaquePartial 3 = 9 := by conv => lhs; cbv

/-! Opaque constant used as argument to a non-opaque function stays opaque. -/

def double (n : Nat) : Nat := n + n

/--
error: unsolved goals
⊢ (match pureOpaque, pureOpaque with
    | a, Nat.zero => a
    | a, b.succ => (a.add b).succ) =
    14
-/
#guard_msgs in
example : double pureOpaque = 14 := by conv => lhs; cbv
