/-!
# Proper handling of delayed assignment metavariables in `match` elaboration

https://github.com/leanprover/lean4/issues/6354
-/

namespace Test1
/-!
Simplified version of example from issue 6354.
Previously, had error `(kernel) declaration has metavariables '_example'`
-/

structure A where
  p: Prop
  q: True

example := (λ ⟨_,_⟩ ↦ True.intro : (A.mk (And True True) (by exact True.intro)).p → True)

end Test1


namespace Test2
/-!
Example from issue (by @roos-j)
-/

structure A where
  p: Prop
  q: True

structure B extends A where
  q': p → True

example: B where
  p := True ∧ True
  q := by exact True.intro
  q' := λ ⟨_,_⟩ ↦ True.intro

end Test2


namespace Test3
/-!
Example from issue comment (by @b-mehta)
-/

class Preorder (α : Type) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  lt := fun a b => a ≤ b ∧ ¬b ≤ a

class PartialOrder (α : Type) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

inductive MyOrder : Nat × Nat → Nat × Nat → Prop
  | within {x u m : Nat} : x ≤ u → MyOrder (x, m) (u, m)

instance : PartialOrder (Nat × Nat) where
  le := MyOrder
  le_refl x := .within (Nat.le_refl _)
  le_antisymm | _, _, .within _, .within _ => Prod.ext (Nat.le_antisymm ‹_› ‹_›) rfl

end Test3
