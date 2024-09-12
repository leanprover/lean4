/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
prelude
import Init.Core

namespace Sum

deriving instance DecidableEq for Sum
deriving instance BEq for Sum

/-- Check if a sum is `inl` and if so, retrieve its contents. -/
def getLeft? : α ⊕ β → Option α
  | inl a => some a
  | inr _ => none

/-- Check if a sum is `inr` and if so, retrieve its contents. -/
def getRight? : α ⊕ β → Option β
  | inr b => some b
  | inl _ => none

/-- Define a function on `α ⊕ β` by giving separate definitions on `α` and `β`. -/
protected def elim {α β γ} (f : α → γ) (g : β → γ) : α ⊕ β → γ :=
  fun x => Sum.casesOn x f g

@[simp] theorem elim_inl (f : α → γ) (g : β → γ) (x : α) :
    Sum.elim f g (inl x) = f x := rfl

@[simp] theorem elim_inr (f : α → γ) (g : β → γ) (x : β) :
    Sum.elim f g (inr x) = g x := rfl

end Sum
