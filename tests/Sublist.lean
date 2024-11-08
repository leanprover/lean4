/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
  Kim Morrison
-/
prelude
import Init.Data.List.TakeDrop

/-!
# Lemmas about `List.Subset`, `List.Sublist`, `List.IsPrefix`, `List.IsSuffix`, and `List.IsInfix`.
-/

namespace List

open Nat

/-! ### isPrefixOf -/
section isPrefixOf
variable [BEq α]

@[simp] theorem isPrefixOf_cons₂_self [LawfulBEq α] {a : α} :
    isPrefixOf (a::as) (a::bs) = isPrefixOf as bs := by simp [isPrefixOf_cons₂]
