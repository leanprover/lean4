/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.HasCoe -- import legacy HasCoe
import Init.Core

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

abbrev coeB {α : Sort u} {β : Sort v} (a : α) [Coe α β] : β :=
@Coe.coe α β _ a

abbrev coeD {α : Sort u} {β : Sort v} (a : α) [CoeDep α a β] : β :=
@CoeDep.coe α a β _

/-- Apply coercion manually. -/
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

instance coeDecidableEq (x : Bool) : Decidable (coe x) :=
inferInstanceAs (Decidable (x = true))

instance decPropToBool (p : Prop) [Decidable p] : CoeDep Prop p Bool :=
{ coe := decide p }

instance optionCoe {α : Type u} : Coe α (Option α) :=
{ coe := some }

instance subtypeCoe {α : Sort u} {p : α → Prop} (v : { x // p x }) : CoeT { x // p x } v α :=
{ coe := v.val }
