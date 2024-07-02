/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Init.Data.List.Lemmas

namespace List

/-- `O(n)`. Partial map. If `f : Π a, P a → β` is a partial function defined on
  `a : α` satisfying `P`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `P`, using the proof
  to apply `f`. -/
@[simp] def pmap {P : α → Prop} (f : ∀ a, P a → β) : ∀ l : List α, (H : ∀ a ∈ l, P a) → List β
  | [], _ => []
  | a :: l, H => f a (forall_mem_cons.1 H).1 :: pmap f l (forall_mem_cons.1 H).2

/--
Unsafe implementation of `attachWith`, taking advantage of the fact that the representation of
`List {x // P x}` is the same as the input `List α`.
(Someday, the compiler might do this optimization automatically, but until then...)
-/
@[inline] private unsafe def attachWithImpl
    (l : List α) (P : α → Prop) (_ : ∀ x ∈ l, P x) : List {x // P x} := unsafeCast l

/-- `O(1)`. "Attach" a proof `P x` that holds for all the elements of `l` to produce a new list
  with the same elements but in the type `{x // P x}`. -/
@[implemented_by attachWithImpl] def attachWith
    (l : List α) (P : α → Prop) (H : ∀ x ∈ l, P x) : List {x // P x} := pmap Subtype.mk l H

/-- `O(1)`. "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
@[inline] def attach (l : List α) : List {x // x ∈ l} := attachWith l _ fun _ => id

/-- Implementation of `pmap` using the zero-copy version of `attach`. -/
@[inline] private def pmapImpl {P : α → Prop} (f : ∀ a, P a → β) (l : List α) (H : ∀ a ∈ l, P a) :
    List β := (l.attachWith _ H).map fun ⟨x, h'⟩ => f x h'

@[csimp] private theorem pmap_eq_pmapImpl : @pmap = @pmapImpl := by
  funext α β p f L h'
  let rec go : ∀ L' (hL' : ∀ ⦃x⦄, x ∈ L' → p x),
      pmap f L' hL' = map (fun ⟨x, hx⟩ => f x hx) (pmap Subtype.mk L' hL')
  | nil, hL' => rfl
  | cons _ L', hL' => congrArg _ <| go L' fun _ hx => hL' (.tail _ hx)
  exact go L h'
