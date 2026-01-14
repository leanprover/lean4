module
abbrev F : Fin 3 → Nat
| 0 => 0
| 1 => 1
| 2 => 2

abbrev Pairwise (r : α → α → Prop) :=
  ∀ ⦃i j⦄, i ≠ j → r i j

abbrev onFun (f : β → β → φ) (g : α → β) : α → α → φ := fun x y => f (g x) (g y)

example : Pairwise (onFun (fun a b => a + b < 10) fun x ↦ F x) := by
  grind
