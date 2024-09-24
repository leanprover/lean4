/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Entails
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
This module contains the definition of the `Formula` typeclass. It is the interface that needs to
be satisfied by any LRAT implementation that can be used by the generic `LRATChecker` module.
-/

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

open Std.Sat

/--
Typeclass for formulas. An instance `[Formula α β σ]` indicates that `σ` is the type of a formula
with variables of type `α`, clauses of type `β`, and clause ids of type `Nat`.
-/
class Formula (α : outParam (Type u)) (β : outParam (Type v)) [Clause α β] (σ : Type w) [Entails α σ] where
  /-- A function used exclusively for defining Formula's satisfiability semantics. -/
  toList : σ → List β
  /-- A predicate that indicates whether a formula can soundly be passed into performRupAdd. -/
  ReadyForRupAdd : σ → Prop
  /-- A predicate that indicates whether a formula can soundly be passed into performRatAdd. -/
  ReadyForRatAdd : σ → Prop
  ofArray : Array (Option β) → σ
  readyForRupAdd_ofArray : ∀ arr : Array (Option β), ReadyForRupAdd (ofArray arr)
  readyForRatAdd_ofArray : ∀ arr : Array (Option β), ReadyForRatAdd (ofArray arr)
  insert : σ → β → σ
  insert_iff : ∀ f : σ, ∀ c1 : β, ∀ c2 : β,
    c2 ∈ toList (insert f c1) ↔ c2 = c1 ∨ c2 ∈ toList f
  readyForRupAdd_insert : ∀ f : σ, ∀ c : β, ReadyForRupAdd f → ReadyForRupAdd (insert f c)
  readyForRatAdd_insert : ∀ f : σ, ∀ c : β, ReadyForRatAdd f → ReadyForRatAdd (insert f c)
  delete : σ → Array Nat → σ
  delete_subset : ∀ f : σ, ∀ arr : Array Nat, ∀ c : β,
    c ∈ toList (delete f arr) → c ∈ toList f
  readyForRupAdd_delete : ∀ f : σ, ∀ arr : Array Nat, ReadyForRupAdd f → ReadyForRupAdd (delete f arr)
  readyForRatAdd_delete : ∀ f : σ, ∀ arr : Array Nat, ReadyForRatAdd f → ReadyForRatAdd (delete f arr)
  formulaEntails_def : ∀ p : α → Bool, ∀ f : σ, Entails.eval p f = (toList f).all (fun c => p ⊨ c)
  performRupAdd : σ → β → Array Nat → σ × Bool
  rupAdd_result : ∀ f : σ, ∀ c : β, ∀ rupHints : Array Nat, ∀ f' : σ,
    ReadyForRupAdd f → performRupAdd f c rupHints = (f', true) → f' = insert f c
  rupAdd_sound : ∀ f : σ, ∀ c : β, ∀ rupHints : Array Nat, ∀ f' : σ,
    ReadyForRupAdd f → performRupAdd f c rupHints = (f', true) → Liff α f f'
  performRatAdd : σ → β → Literal α → Array Nat → Array (Nat × Array Nat) → σ × Bool
  ratAdd_result :
    ∀ f : σ, ∀ c : β, ∀ p : Literal α, ∀ rupHints : Array Nat, ∀ ratHints : Array (Nat × Array Nat), ∀ f' : σ,
    ReadyForRatAdd f → p ∈ Clause.toList c → performRatAdd f c p rupHints ratHints = (f', true) → f' = insert f c
  ratAdd_sound :
    ∀ f : σ, ∀ c : β, ∀ p : Literal α, ∀ rupHints : Array Nat, ∀ ratHints : Array (Nat × Array Nat), ∀ f' : σ,
    ReadyForRatAdd f → p ∈ Clause.toList c → performRatAdd f c p rupHints ratHints = (f', true) → Equisat α f f'

end Internal
end LRAT
end Std.Tactic.BVDecide
