prelude
import Init.Data.Nat.Basic

universes u v w

class Coe (α : Sort u) (β : Sort v) :=
(coe : α → β)

class CoeDep (α : Sort u) (a : α) (β : Sort v) :=
(coe : β)

/-- Auxiliary class that contains the transitive closure of `Coe` and `CoeDep`. -/
class CoeT (α : Sort u) (a : α) (β : Sort v) :=
(coe : β)

class CoeFun (α : Sort u) (a : α) (γ : outParam (Sort v)) :=
(coe : γ)

class CoeSort (α : Sort u) (a : α) (β : outParam (Sort v)) :=
(coe : β)

-- Base case
abbrev coeB {α : Sort u} {β : Sort v} (a : α) [Coe α β] : β :=
@Coe.coe α β _ a

abbrev coeD {α : Sort u} {β : Sort v} (a : α) [CoeDep α a β] : β :=
@CoeDep.coe α a β _

abbrev coe {α : Sort u} {β : Sort v} (a : α) [CoeT α a β] : β :=
@CoeT.coe α a β _

abbrev coeFun {α : Sort u} {γ : Sort v} (a : α) [CoeFun α a γ] : γ :=
@CoeFun.coe α a γ _

abbrev coeSort {α : Sort u} {γ : Sort v} (a : α) [CoeSort α a γ] : γ :=
@CoeSort.coe α a γ _

instance coeDepTrans {α : Sort u} {β : Sort v} {δ : Sort w} (a : α) [CoeT α a β] [CoeDep β (coe a) δ] : CoeT α a δ :=
{ coe := coeD (coe a : β) }

instance coeTrans {α : Sort u} {β : Sort v} {δ : Sort w} (a : α) [CoeT α a β] [Coe β δ] : CoeT α a δ :=
{ coe := coeB (coe a : β) }

instance coeBase {α : Sort u} {β : Sort v} (a : α) [Coe α β] : CoeT α a β :=
{ coe := coeB a }

instance coeDepBase {α : Sort u} {β : Sort v} (a : α) [CoeDep α a β] : CoeT α a β :=
{ coe := coeD a }

instance coeFunTrans {α : Sort u} {β : Sort v} {γ : Sort w} (a : α) [CoeT α a β] [CoeFun β (coe a) γ] : CoeFun α a γ :=
{ coe := coeFun (coe a : β) }

instance coeSortTrans {α : Sort u} {β : Sort v} {δ : Sort w} (a : α) [CoeT α a β] [CoeSort β (coe a) δ] : CoeFun α a δ :=
{ coe := coeSort (coe a : β) }

/- Basic instances -/

instance boolToProp : Coe Bool Prop :=
{ coe := fun b => b = true }

instance decPropToBool (p : Prop) [Decidable p] : CoeDep Prop p Bool :=
{ coe := decide p }

instance optionCoe {α : Type u} : Coe α (Option α) :=
{ coe := some }

instance subtypeCoe {α : Sort u} {p : α → Prop} (v : { x // p x }) : CoeT { x // p x } v α :=
{ coe := v.val }

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

#synth CoeT Nat 0 (Option (Option (Option (Option (Option Nat)))))
#synth CoeT { x : Nat // x > 0 } ⟨1, sorryAx _⟩ Nat
#synth CoeT { x : Nat // x > 0 } ⟨1, sorryAx _⟩ Bool
#synth CoeT Nat 0 (Option Nat)
#synth CoeT Nat 0 (Option (Option Nat))
#synth CoeT Nat 0 (Option (Option (Option Nat)))
#synth CoeT Prop (0 = 1) Nat
#synth CoeT Bool true (Option Nat)

variables (f : ConstantFunction _ _)
#synth CoeFun (ConstantFunction _ _) f _

-- #synth CoeT Bool true (Option (Nat × Nat)) -- fail quickly
