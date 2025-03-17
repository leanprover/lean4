/-!
# Generalize `elab_as_elim` to allow arbitrary motive applications
-/

/-!
The following eliminator isn't valid for `induction`/`cases` since the return type
has `motive` applied to `Int.natAbs i`, which isn't a parameter,
but this is not a problem for `elab_as_elim`.
-/

@[elab_as_elim]
theorem natAbs_elim {motive : Nat → Prop} (i : Int)
  (hpos : ∀ (n : Nat), i = n → motive n)
  (hneg : ∀ (n : Nat), i = -↑n → motive n) :
  motive (Int.natAbs i) := by sorry

example (x : Int) (y : Nat) : x.natAbs < y := by
  refine natAbs_elim x ?_ ?_
  · guard_target = ∀ (n : Nat), x = ↑n → n < y
    sorry
  · guard_target = ∀ (n : Nat), x = -↑n → n < y
    sorry

example (x : Int) (y : Nat) : (x + 1).natAbs + 1 < y := by
  refine natAbs_elim (x + 1) ?_ ?_
  · guard_target = ∀ (n : Nat), x + 1 = ↑n → n + 1 < y
    sorry
  · guard_target = ∀ (n : Nat), x + 1 = -↑n → n + 1 < y
    sorry

/-!
The target can be inferred from the expected type.
-/
example (x : Int) (y : Nat) : (x + 1).natAbs < y := by
  refine natAbs_elim _ ?_ ?_
  · guard_target = ∀ (n : Nat), x + 1 = ↑n → n < y
    sorry
  · guard_target = ∀ (n : Nat), x + 1 = -↑n → n < y
    sorry
