import Lean

/-!
# `.implicit` transparency bump for lambda binder types in `isDefEq`

The binder type of a `fun` is usually inferred rather than written by the user, so it is,
morally, implicit type information. Like implicit arguments, the binder types of two lambda
expressions are therefore compared at (at least) `.implicit` transparency, so that
`[implicit_reducible]` definitions unfold even when the ambient transparency is lower.
The bump is controlled by the option `backward.isDefEq.lambdaBump` (default: `true`) and
does not apply to the binder types of `∀` binders.
-/

open Lean Meta

def A := Nat  -- semireducible
def C := Nat  -- semireducible
@[implicit_reducible] def B := Nat

/-- `fun x : dom => x` -/
def mkLamId (dom : Name) : Expr := .lam `x (mkConst dom) (.bvar 0) .default

/-- `(x : dom) → True` -/
def mkTrivialForall (dom : Name) : Expr := .forallE `x (mkConst dom) (mkConst ``True) .default

/-!
With the default options, the `[implicit_reducible]` definition `B` unfolds when comparing
lambda binder types, even at ambient `.reducible` transparency.
-/

/-- info: true -/
#guard_msgs in
run_meta logInfo m!"{← withReducible <| isDefEq (mkLamId ``B) (mkLamId ``Nat)}"

/-!
Disabling `backward.isDefEq.lambdaBump` disables the bump, so the binder types are compared
at the ambient transparency.
-/

/-- info: false -/
#guard_msgs in
set_option backward.isDefEq.lambdaBump false in
run_meta logInfo m!"{← withReducible <| isDefEq (mkLamId ``B) (mkLamId ``Nat)}"

/-!
`backward.isDefEq.respectTransparency := false` restores the old behavior wholesale, which had
no bump for lambda binder types.
-/

/-- info: false -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency false in
run_meta logInfo m!"{← withReducible <| isDefEq (mkLamId ``B) (mkLamId ``Nat)}"

/-!
The bump is to `.implicit`, not `.default`: semireducible definitions still do not unfold.
-/

/-- info: false -/
#guard_msgs in
run_meta logInfo m!"{← withReducible <| isDefEq (mkLamId ``A) (mkLamId ``C)}"

/-- info: true -/
#guard_msgs in
run_meta logInfo m!"{← isDefEq (mkLamId ``A) (mkLamId ``C)}"

/-!
`∀` binder types are visible parts of a type and are not bumped.
-/

/-- info: false -/
#guard_msgs in
run_meta logInfo m!"{← withReducible <| isDefEq (mkTrivialForall ``B) (mkTrivialForall ``Nat)}"

/-- info: true -/
#guard_msgs in
run_meta logInfo m!"{← withTransparency .implicit <| isDefEq (mkTrivialForall ``B) (mkTrivialForall ``Nat)}"

/-!
In a mixed `fun`/`∀` binder chain, only the `fun` binder types are bumped.
-/

/-- info: true -/
#guard_msgs in
run_meta do
  let mkE (dom : Name) : Expr := .lam `p (mkConst dom) (mkTrivialForall ``Nat) .default
  logInfo m!"{← withReducible <| isDefEq (mkE ``B) (mkE ``Nat)}"

/-- info: false -/
#guard_msgs in
run_meta do
  let mkE (dom : Name) : Expr := .lam `p (mkConst ``Nat) (mkTrivialForall dom) .default
  logInfo m!"{← withReducible <| isDefEq (mkE ``B) (mkE ``Nat)}"

/-!
End-to-end: a `simp` lemma whose left-hand side contains a lambda applies to a goal where the
lambda's binder type matches only after unfolding an `[implicit_reducible]` definition.
-/

def g (f : Nat → Nat) : Nat := f 0

@[simp] theorem g_eq : g (fun x : B => x) = 0 := rfl

#guard_msgs in
example : g (fun x : Nat => x) = 0 := by simp only [g_eq]

/-- error: `simp` made no progress -/
#guard_msgs in
set_option backward.isDefEq.lambdaBump false in
example : g (fun x : Nat => x) = 0 := by simp only [g_eq]
