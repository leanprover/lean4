/-!
Regression test for #16120: `Sym.shareCommon` must not merge two `have`/`let` terms that differ only
in their type. Merging them produced ill-scoped proofs that the kernel rejected.
-/

theorem m1 (n : Nat) :
    (∀ (a b : Nat) (x : Fin a), (have y : Fin a := x; y) = (have y : Fin a := x; y)) ∧
    (∀ (x : Fin n), (have y : Fin n := x; y) = (have y : Fin n := x; y)) := by
  sym =>
    apply And.intro
    · intro a b x
      apply Eq.refl
    · intro x
      apply Eq.refl

theorem m2 (n : Nat) :
    (∀ (a b : Nat) (x : Fin a), (let y : Fin a := x; y) = (let y : Fin a := x; y)) ∧
    (∀ (x : Fin n), (let y : Fin n := x; y) = (let y : Fin n := x; y)) := by
  sym =>
    apply And.intro
    · intro a b x
      apply Eq.refl
    · intro x
      apply Eq.refl
