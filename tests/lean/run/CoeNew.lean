

universe u v w

instance boolToNat : Coe Bool Nat :=
{ coe := fun b => cond b 1 0 }

instance natToBool : Coe Nat Bool :=
{ coe := fun n => match n with
  | 0 => false
  | _ => true }

structure ConstantFunction (α β : Type) :=
(f : α → β)
(h : ∀ a₁ a₂, f a₁ = f a₂)

instance constantFunctionCoe {α β : Type} : CoeFun (ConstantFunction α β) (fun _ => α → β) :=
{ coe := fun c => c.f }

set_option pp.explicit true

#synth CoeT { x : Nat // x > 0 } ⟨1, sorryAx _ false⟩ Nat
#synth CoeT { x : Nat // x > 0 } ⟨1, sorryAx _ false⟩ Bool
#synth CoeT Nat 0 (Option Nat)
#synth CoeT Bool true (Option Nat)
#synth CoeT Prop (0 = 1) Bool
#synth CoeT Bool true (Option Nat)

def f (c : ConstantFunction Nat Nat) : Nat :=
c 0
