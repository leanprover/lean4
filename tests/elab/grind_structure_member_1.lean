module

@[expose] public section

open Function

structure Equiv (α : Sort _) (β : Sort _) where
  toFun : α → β
  invFun : β → α
  left_inv : LeftInverse invFun toFun
  right_inv : RightInverse invFun toFun


infixl:25 " ≃ " => Equiv

namespace Equiv

set_option grind.debug true in
protected def cast {α β : Sort _} (h : α = β) : α ≃ β where
  toFun := cast h
  invFun := cast h.symm
  left_inv := by grind
  right_inv := by grind

