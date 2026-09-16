/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Init.Internal.Order

universe u v
@[expose] public section

/-!
# Additional operations of a complete lattice

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
noncomputable def iInf {ι : Type v} (f : ι → α) : α := inf (fun x => ∃ i, f i = x)

open Lean in
@[inherit_doc iInf] scoped macro "⨅ " bs:Lean.explicitBinders ", " b:term : term => do
  return ⟨← Lean.expandExplicitBinders ``iInf bs b⟩

/-- Indexed supremum -/
noncomputable def iSup {ι : Type v} (f : ι → α) : α :=
  CompleteLattice.sup (fun x => ∃ i, f i = x)

open Lean in
@[inherit_doc iSup] scoped macro "⨆ " bs:Lean.explicitBinders ", " b:term : term => do
  return ⟨← Lean.expandExplicitBinders ``iSup bs b⟩

end Lean.Order
