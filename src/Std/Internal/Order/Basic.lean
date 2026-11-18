/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Init.Internal.Order
import Init.Classical

universe u v
@[expose] public section

/-!
# Complete lattices

The definitions and instances of the lattice theory: the operations of a complete lattice, the
complete lattice of propositions, the embedding `⌜·⌝` of propositions, supremum-preserving maps with
their upper adjoints, and Heyting implication `⇨`.

## Additional operations of a complete lattice

The top element `⊤`, the binary meet `⊓` and join `⊔`, and the indexed infimum `⨅` and supremum
`⨆`. The bottom element `⊥` comes from `CCPO`, which every complete lattice is.
-/

namespace Lean.Order

attribute [refl] PartialOrder.rel_refl

variable {α : Type u} [CompleteLattice α]

/-- Top element of a complete lattice (supremum of all elements) -/
noncomputable def top : α := CompleteLattice.sup (fun _ => True)

@[inherit_doc top]
scoped notation "⊤" => top

/-- A complete lattice is a chain-complete partial order. -/
noncomputable scoped instance instCCPOOfCompleteLattice : CCPO α where
  has_csup {c} _ := CompleteLattice.has_sup c

/-- Binary meet (infimum) -/
noncomputable def meet (x y : α) : α := inf (fun z => z = x ∨ z = y)

@[inherit_doc meet]
scoped infixl:70 " ⊓ " => meet

/-- Binary join (supremum) -/
noncomputable def join (x y : α) : α := CompleteLattice.sup (fun z => z = x ∨ z = y)

@[inherit_doc join]
scoped infixl:65 " ⊔ " => join

/-- Indexed infimum -/
noncomputable def iInf {ι : Sort v} (f : ι → α) : α := inf (fun x => ∃ i, f i = x)

open Lean in
@[inherit_doc iInf] scoped macro "⨅ " bs:Lean.explicitBinders ", " b:term : term => do
  return ⟨← Lean.expandExplicitBinders ``iInf bs b⟩

/-- Indexed supremum -/
noncomputable def iSup {ι : Sort v} (f : ι → α) : α :=
  CompleteLattice.sup (fun x => ∃ i, f i = x)

open Lean in
@[inherit_doc iSup] scoped macro "⨆ " bs:Lean.explicitBinders ", " b:term : term => do
  return ⟨← Lean.expandExplicitBinders ``iSup bs b⟩

end Lean.Order

/-!
## The complete lattice of propositions

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

/-!
## Embedding of propositions

`⌜p⌝` embeds a proposition `p` into an assertion lattice as `⊤` if `p` holds and `⊥` otherwise.
-/

namespace Lean.Order

open _root_.Classical in
/-- Embedding of propositions into an CompleteLattice type. `⌜p⌝` embeds `p : Prop` as `⊤` if `p` holds
and `⊥` otherwise. -/
noncomputable def CompleteLattice.ofProp [CompleteLattice l] (p : Prop) : l :=
  if p then ⊤ else ⊥

@[inherit_doc CompleteLattice.ofProp]
scoped notation "⌜" p "⌝" => CompleteLattice.ofProp p

/-!
## Supremum-preserving maps and Heyting implication

A supremum-preserving map on a complete lattice is a lower adjoint. Its upper adjoint is the
implication belonging to it: Heyting `⇨` for the lattice meet, a magic wand for a separating
conjunction.
-/

section

variable {α : Type u} [CompleteLattice α]

/--
`f : α → α` *preserves suprema* if it distributes over arbitrary suprema:
`f (sup s) = sup { f x | x ∈ s }`. Equivalently `f` is a lower adjoint, so it has an upper adjoint
`PreservesSup.upperAdjoint f`.

A frame operator acts by a supremum-preserving map for each resource `r`: the lattice meet
`(a ⊓ ·)`,
or a cost combinator `(costConj r)` for a counter resource. The upper adjoint is the corresponding
implication: Heyting `⇨` for the meet, a magic wand for separating conjunction.
-/
class PreservesSup {α : Type u} [CompleteLattice α] (f : α → α) : Prop where
  /-- `f` preserves joins. -/
  map_sup (s : α → Prop) :
    f (CompleteLattice.sup s) = CompleteLattice.sup (fun y => ∃ x, s x ∧ y = f x)

namespace PreservesSup

/-- The upper adjoint of `f`: the join of all `x` with `f x ⊑ b`. For `f = (a ⊓ ·)` this is Heyting
implication `a ⇨ ·`. -/
noncomputable def upperAdjoint (f : α → α) (b : α) : α := CompleteLattice.sup (fun x => f x ⊑ b)

/-- Unit, free from the definition of `upperAdjoint`: `f x ⊑ b → x ⊑ upperAdjoint f b`. Needs only
`CompleteLattice`. -/
theorem le_upperAdjoint (f : α → α) {b x : α} (h : f x ⊑ b) : x ⊑ upperAdjoint f b :=
  le_sup (c := fun x : α => f x ⊑ b) h

end PreservesSup

/-- A complete lattice whose meets preserve suprema. The Heyting implication `⇨` is then a right
adjoint, and `⊓` distributes over suprema of arbitrary families. The literature also calls such a
lattice a frame. -/
abbrev Heyting (α : Type u) [CompleteLattice α] : Prop := ∀ a : α, PreservesSup (meet a)

/-- Heyting implication: the upper adjoint of the lattice meet. For `Prop` it is `→`. -/
noncomputable def himp {α : Type u} [CompleteLattice α] (a b : α) : α :=
  PreservesSup.upperAdjoint (meet a) b

@[inherit_doc himp] scoped infixr:60 " ⇨ " => himp

end

end Lean.Order
