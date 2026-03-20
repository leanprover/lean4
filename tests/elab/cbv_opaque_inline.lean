set_option cbv.warning false

/-! Test that `@[cbv_opaque]` is respected for `@[inline]` and `@[always_inline]` definitions.
These are reducible, so the preprocessing stage must skip them when they are also `@[cbv_opaque]`. -/

/-! ## `@[inline]` + `@[cbv_opaque]` -/

@[inline, cbv_opaque] def inlineSecret : Nat := 42

/--
error: unsolved goals
⊢ inlineSecret = 42
-/
#guard_msgs in
example : inlineSecret = 42 := by conv => lhs; cbv

@[inline, cbv_opaque] def inlineAdd (a b : Nat) : Nat := a + b

/--
error: unsolved goals
⊢ inlineAdd 1 2 = 3
-/
#guard_msgs in
example : inlineAdd 1 2 = 3 := by conv => lhs; cbv

/-! ## `@[always_inline]` + `@[cbv_opaque]` -/

@[always_inline, cbv_opaque] def alwaysInlineSecret : Nat := 99

/--
error: unsolved goals
⊢ alwaysInlineSecret = 99
-/
#guard_msgs in
example : alwaysInlineSecret = 99 := by conv => lhs; cbv

@[always_inline, cbv_opaque] def alwaysInlineMul (a b : Nat) : Nat := a * b

/--
error: unsolved goals
⊢ alwaysInlineMul 3 4 = 12
-/
#guard_msgs in
example : alwaysInlineMul 3 4 = 12 := by conv => lhs; cbv

/-! ## `@[cbv_eval]` overrides `@[cbv_opaque]` even for inline definitions -/

@[inline, cbv_opaque] def inlineOpaqueAdd (a b : Nat) : Nat := a + b
@[cbv_eval] theorem inlineOpaqueAdd_eq (a b : Nat) : inlineOpaqueAdd a b = a + b := rfl

example : inlineOpaqueAdd 1 2 = 3 := by conv => lhs; cbv

@[always_inline, cbv_opaque] def alwaysInlineOpaqueMul (a b : Nat) : Nat := a * b
@[cbv_eval] theorem alwaysInlineOpaqueMul_eq (a b : Nat) : alwaysInlineOpaqueMul a b = a * b := rfl

example : alwaysInlineOpaqueMul 3 4 = 12 := by conv => lhs; cbv

/-! ## Inline definitions without `@[cbv_opaque]` still unfold normally -/

@[inline] def inlineNormal (n : Nat) : Nat := n + 1

example : inlineNormal 5 = 6 := by cbv

@[always_inline] def alwaysInlineNormal (n : Nat) : Nat := n * 2

example : alwaysInlineNormal 5 = 10 := by cbv

/-! ## `@[cbv_opaque]` + `@[inline]` with `cbvGoal` (uses `preprocessMVar`) -/

/-- The kernel's `isDefEq` in `cbvGoal` still closes inline opaque goals. -/
example : inlineSecret = 42 := by cbv
example : alwaysInlineSecret = 99 := by cbv

/-! ## `@[cbv_opaque]` + `@[inline]` used as argument to a non-opaque function -/

def mySucc (n : Nat) : Nat := n + 1

/--
error: unsolved goals
⊢ inlineSecret.succ = 43
-/
#guard_msgs in
example : mySucc inlineSecret = 43 := by conv => lhs; cbv

/-! ## Pattern matching on `@[cbv_opaque]` + `@[inline]` discriminant gets stuck -/

def isEven : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => isEven n

/--
error: unsolved goals
⊢ (match inlineSecret with
    | 0 => true
    | 1 => false
    | a.succ.succ => isEven a) =
    true
-/
#guard_msgs in
example : isEven inlineSecret = true := by conv => lhs; cbv

/-! ## Projections on `@[cbv_opaque]` + `@[inline]` structures are not reduced -/

@[inline, cbv_opaque] def inlinePair : Nat × Nat := (10, 20)

/--
error: unsolved goals
⊢ inlinePair.1 = 10
-/
#guard_msgs in
example : inlinePair.1 = 10 := by conv => lhs; cbv

/-! ## `decide_cbv` with `@[cbv_opaque]` + `@[inline]` -/

@[inline, cbv_opaque] def inlineBoolVal : Bool := true
@[cbv_eval] theorem inlineBoolVal_eq : inlineBoolVal = true := rfl

example : inlineBoolVal = true := by decide_cbv

/-! Without `@[cbv_eval]`, `decide_cbv` gets stuck on inline opaque -/

@[inline, cbv_opaque] def inlineBoolStuck : Bool := true

#guard_msgs (drop error) in
example : inlineBoolStuck = true := by decide_cbv
