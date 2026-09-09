/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Init.Internal.Order.Basic

@[expose] public section

/-!
# The complete lattice of propositions

`⊑` is implication and the supremum of a set of propositions is the existential quantifier over it.

The instances are `scoped` in `Std.Internal.Order`, outside of `Lean.Order`. `partial_fixpoint` and
`coinductive_fixpoint` order `Prop` by `ImplicationOrder` and `ReverseImplicationOrder`, and their
monotonicity lemmas live in `Lean.Order` itself. Open `Std.Internal.Order` to order `Prop` by
implication.
-/

namespace Std.Internal.Order

open Lean.Order

scoped instance instPartialOrderProp : PartialOrder Prop where
  rel p q := p → q
  rel_refl := id
  rel_trans := fun h1 h2 x => h2 (h1 x)
  rel_antisymm := fun h1 h2 => propext ⟨h1, h2⟩

/-- Supremum for Prop: true iff some element of the set is true -/
def propSup (c : Prop → Prop) : Prop := ∃ p, c p ∧ p

theorem propSup_is_sup (c : Prop → Prop) : is_sup c (propSup c) := by
  intro y
  constructor
  · intro hsup z hcz hz
    apply hsup
    exact Exists.intro z (And.intro hcz hz)
  · intro h ⟨z, hcz, hz⟩
    exact h z hcz hz

scoped instance instCompleteLatticeProp : CompleteLattice Prop where
  has_sup c := ⟨propSup c, propSup_is_sup c⟩

end Std.Internal.Order
