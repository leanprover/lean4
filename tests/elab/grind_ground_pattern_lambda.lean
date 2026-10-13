module
reset_grind_attrs%

/-!
E-match theorems whose ground pattern arguments contain binders must be activated
as soon as the indexable symbols outside the binders occur in the goal.

`grind` internalizes lambdas and nonparametric literals (`Char`, `Int`, ...) as opaque
terms, but pattern symbol collection descends into them, so `myPred_of_true` below is
indexed by `Nat` and `True` as well as `myPred`, and `fc_a` by `Char.ofNat` as well as `fc`.
The internalizer must therefore mark the constants occurring in such terms as found,
otherwise the theorems are never activated. Reported by Henrik Böving.
-/

def myPred (P : Nat → Prop) : Prop := ∀ n > 1, P n

@[simp, grind .]
theorem myPred_of_true : myPred (fun _ => True) := fun _ _ ↦ trivial

def mySet (_ : Nat) : Prop := True

@[simp, grind .]
theorem mySet_true {n : Nat} : mySet n := trivial

@[grind =]
theorem mySet_iff_true : mySet = (fun _ ↦ True) := funext (by simp)

-- A theorem whose ground pattern mentions a constant that never occurs in the goal, not even under a
-- binder, must remain dormant.
axiom c : Nat → Prop
axiom myPred_of_c : myPred (fun n => c (n + 1))
attribute [grind .] myPred_of_c

set_option trace.grind.ematch true in
example : myPred (fun n ↦ mySet n) := by grind

set_option trace.grind.ematch true in
example : myPred mySet := by grind

-- Symbols occurring in the domain of a binder, and in a non-dependent codomain, are still used for indexing.
def myPred2 (P : Prop) : Prop := P

axiom foo : Nat → Prop
axiom baz : Prop

axiom myPred2_of : myPred2 ((∀ x, foo x) → baz)
attribute [grind .] myPred2_of

set_option trace.grind.ematch true in
example (h : myPred2 ((∀ x, foo x) → baz) → False) (_ : (∀ x, foo x) → baz) : False := by grind

-- Nonparametric literals in ground patterns.
def fc (_ : Char) : Nat := 1
@[grind =] theorem fc_a : fc 'a' = 1 := rfl

set_option trace.grind.ematch true in
example : fc 'a' = 1 := by grind

def fi (_ : Int) : Nat := 1
@[grind =] theorem fi_neg : fi (-2) = 1 := rfl

set_option trace.grind.ematch true in
example : fi (-2) = 1 := by grind

-- `OfNat.ofNat` is not an indexing symbol, so a `Nat` literal must not activate theorems indexed by it.
def fn (_ : Nat) : Nat := 1
theorem fn_ofNat (n : Nat) [OfNat Nat n] : fn (OfNat.ofNat n) = 1 := rfl
grind_pattern fn_ofNat => OfNat.ofNat (α := Nat) n

set_option trace.grind.ematch true in
example (h : fn 5 = 2) : fn 5 ≠ 3 := by grind
