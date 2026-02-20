/-!
# Test that `grind` handles nested mdata from multiple `norm_cast` calls

This is a regression test for https://github.com/leanprover/lean4/issues/11411

The issue was that `norm_cast` adds mdata nodes to expressions, and when called
multiple times it creates nested mdata. The `grind` preprocessing step
`eraseIrrelevantMData` was only stripping one layer of mdata instead of all layers.
-/

-- Minimal WithTop definition
def WithTop (α : Type u) := Option α

namespace WithTop

variable {α : Type u}

@[coe] def some : α → WithTop α := Option.some

instance : Coe α (WithTop α) := ⟨some⟩

instance : NatCast (WithTop Nat) where
  natCast n := some n

end WithTop

-- AtLeastTwo infrastructure (from Mathlib.Data.Nat.Init)
class Nat.AtLeastTwo (n : Nat) : Prop where
  prop : n ≥ 2

instance Nat.instAtLeastTwo : Nat.AtLeastTwo (n + 2) where
  prop := Nat.le_add_left 2 n

-- OfNat instance for numeric literals ≥ 2 (from Mathlib.Data.Nat.Cast.Defs)
instance instOfNatAtLeastTwo {R : Type u} [NatCast R] (n : Nat) [Nat.AtLeastTwo n] : OfNat R n where
  ofNat := n

-- The key norm_cast lemma (from Mathlib.Data.Nat.Cast.Defs)
@[simp, norm_cast]
theorem Nat.cast_ofNat {R : Type u} {n : Nat} [NatCast R] [Nat.AtLeastTwo n] :
    (Nat.cast (no_index (OfNat.ofNat n)) : R) = no_index (OfNat.ofNat n) := rfl

variable {Foo : WithTop Nat → Prop} {Bar : Prop}

-- Works: grind without norm_cast
example (foo_imp_bar : ∀ x, Foo x → Bar) (h : Foo 2) : Bar := by
  grind

-- Works: grind after one norm_cast
example (foo_imp_bar : ∀ x, Foo x → Bar) (h : Foo 2) : Bar := by
  norm_cast at h
  grind

-- Previously failed: grind after two norm_casts
-- This used to fail with "unexpected metadata found during internalization"
example (foo_imp_bar : ∀ x, Foo x → Bar) (h : Foo 2) : Bar := by
  norm_cast at h
  norm_cast at h
  grind
