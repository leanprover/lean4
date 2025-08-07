import Init.Data.Order.Factories

open Std

public instance {α : Type u} [LE α] [LT α] (h : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a) : PreorderPackage α := .ofLE α {
  lawful_lt := by
    letI : OrderData α := .ofLE α
    apply LawfulOrderLT.mk

}

example [LE α] : PreorderPackage α := inferInstance
