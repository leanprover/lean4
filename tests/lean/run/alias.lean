def Set (α : Type) := α → Prop

def Set.union (s₁ s₂ : Set α) : Set α :=
  fun a => s₁ a ∨ s₂ a

def FinSet (n : Nat) := Fin n → Prop

namespace FinSet
  export Set (union)
end FinSet

example (x y : FinSet 10) : FinSet 10 :=
  FinSet.union x y

example (x y : FinSet 10) : FinSet 10 :=
  x.union y
