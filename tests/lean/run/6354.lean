import Lean
/-!
# Proper handling of delayed assignment metavariables in `match` elaboration

https://github.com/leanprover/lean4/issues/5925
https://github.com/leanprover/lean4/issues/6354

These all had the error `(kernel) declaration has metavariables '_example'`
due to underapplied delayed assignment metavariables never being instantiated.
-/

namespace Test1
/-!
Simplified version of example from issue 6354.
-/

structure A where
  p: Prop
  q: True

example := (λ ⟨_,_⟩ ↦ True.intro : (A.mk (And True True) (by exact True.intro)).p → True)

end Test1


namespace Test2
/-!
Example from issue 6354 (by @roos-j)
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
Example from issue 6354 (by @b-mehta)
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


namespace Test4
/-!
Example from issue 5925 (by @Komyyy)
-/

def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

axiom my_mul_right_injective {M₀ : Type} [Mul M₀] [Zero M₀] {a : M₀} (ha : a ≠ 0) :
  Injective fun (x : M₀) ↦ a * x

def mul2 : { f : Nat → Nat // Injective f } := ⟨fun x : Nat ↦ 2 * x, my_mul_right_injective nofun⟩

end Test4


namespace Test5
/-!
Example from issue 5925 (by @mik-jozef)
-/

structure ValVar (D: Type) where
  d: D
  x: Nat

def Set (T : Type) := T → Prop

structure Salg where
  D: Type
  I: Nat

def natSalg: Salg := { D := Nat, I := 42 }

inductive HasMem (salg: Salg): Set (Set (ValVar salg.D))
| hasMem
  (set: Set (ValVar salg.D))
  (isElem: set ⟨d, x⟩)
:
  HasMem salg set

def valVarSet: Set (ValVar Nat) :=
  fun ⟨d, x⟩ => x = 0 ∧ d = 0 ∧ d ∉ []

-- Needed to add a unification hint to this test
-- because of https://github.com/leanprover/lean4/pull/6024
unif_hint (s : Salg) where
  s =?= natSalg
  |-
  Salg.D s =?= Nat

def valVarSetHasMem: HasMem natSalg valVarSet :=
  HasMem.hasMem
    valVarSet
    (show valVarSet _ from ⟨rfl, rfl, nofun⟩)

end Test5
