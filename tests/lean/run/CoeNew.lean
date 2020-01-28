prelude
import Init.Data.Nat.Basic

universes u v w

class Coe (α : Sort u) (a : α) (β : Sort v) :=
(coe : β)

/-- Auxiliary class that contains the transitive closure of CoeDep. -/
class CoeT (α : Sort u) (a : α) (β : Sort v) :=
(coe : β)

-- Base case
@[inline] def coeB {α : Sort u} {β : Sort v} (a : α) [Coe α a β] : β :=
@Coe.coe α a β _

-- Transitive case
@[inline] def coeT {α : Sort u} {β : Sort v} (a : α) [CoeT α a β] : β :=
@CoeT.coe α a β _

-- User interface
@[inline] def coe {α : Sort u} {β : Sort v} (a : α) [CoeT α a β] : β :=
coeT a

instance decPropToBool (p : Prop) [Decidable p] : Coe Prop p Bool :=
{ coe := decide p }

instance optionCoe {α : Type u} (a : α) : Coe α a (Option α) :=
{ coe := some a }

instance coeTrans {α : Sort u} {β : Sort v} {δ : Sort w} (a : α) [CoeT α a β] [Coe β (coeT a) δ] : CoeT α a δ :=
{ coe := coeB (coeT a : β) }

instance coeBase {α : Sort u} {β : Sort v} (a : α) [Coe α a β] : CoeT α a β :=
{ coe := coeB a }

instance boolToNat (b : Bool) : Coe Bool b Nat :=
{ coe := cond b 1 0 }

new_frontend
set_option pp.implicit true
#synth CoeT Nat 0 (Option Nat)
#synth CoeT Nat 0 (Option (Option Nat))
#synth CoeT Prop (0 = 1) Nat
#synth CoeT Bool true (Option Nat)
-- #synth CoeT Bool true (Option (Nat × Nat)) -- fail quickly
