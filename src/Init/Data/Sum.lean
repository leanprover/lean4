/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
prelude
import Init.Core
import Init.Util

namespace Sum

deriving instance DecidableEq for Sum
deriving instance BEq for Sum

/-- Check if a sum is `inl`. -/
def isLeft : α ⊕ β → Bool
  | inl _ => true
  | inr _ => false

/-- Check if a sum is `inr`. -/
def isRight : α ⊕ β → Bool
  | inl _ => false
  | inr _ => true

/-- Retrieve the contents from a sum known to be `inl`.-/
def getLeft : (ab : α ⊕ β) → ab.isLeft → α
  | inl a, _ => a

/-- Retrieve the contents from a sum known to be `inr`.-/
def getRight : (ab : α ⊕ β) → ab.isRight → β
  | inr b, _ => b

/-- Check if a sum is `inl` and if so, retrieve its contents. -/
def getLeft? : α ⊕ β → Option α
  | inl a => some a
  | inr _ => none

/-- Check if a sum is `inr` and if so, retrieve its contents. -/
def getRight? : α ⊕ β → Option β
  | inr b => some b
  | inl _ => none

@[inline] def getLeft! {α : Type u} [Inhabited α] : α ⊕ β → α
  | inl x => x
  | inr _ => panic! "value is inr"

@[inline] def getRight! {β : Type u} [Inhabited β] : α ⊕ β → β
  | inl _ => panic! "value is inl"
  | inr x => x

@[inline] def lift (f : α → γ) (g : β → γ) : α ⊕ β → γ
  | inl x => f x
  | inr y => g y

end Sum
