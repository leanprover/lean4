universes u v w

instance boolToNat : Coe Bool Nat :=
{ coe := fun b => cond b 1 0 }

instance natToBool : Coe Nat Bool :=
{ coe := fun n => match n with
  | 0 => false
  | _ => true }

structure ConstantFunction (α β : Type) :=
(f : α → β)
(h : ∀ a₁ a₂, f a₁ = f a₂)

instance constantFunctionCoe {α β : Type} (c : ConstantFunction α β) : CoeFun (ConstantFunction α β) c (α → β) :=
{ coe := c.f }

new_frontend
set_option pp.implicit true

#synth CoeT { x : Nat // x > 0 } ⟨1, sorryAx _⟩ Nat
#synth CoeT { x : Nat // x > 0 } ⟨1, sorryAx _⟩ Bool
#synth CoeT Nat 0 (Option Nat)
#synth CoeT Bool true (Option Nat)
#synth CoeT Prop (0 = 1) Nat
#synth CoeT Bool true (Option Nat)

variables (f : ConstantFunction _ _)
#synth CoeFun (ConstantFunction _ _) f _

-- #synth CoeT Bool true (Option (Nat × Nat)) -- fail quickly
