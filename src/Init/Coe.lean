/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core

universes u v w w'

class Coe (α : Sort u) (β : Sort v) :=
  (coe : α → β)

/-- Auxiliary class that contains the transitive closure of `Coe`. -/
class CoeTC (α : Sort u) (β : Sort v) :=
  (coe : α → β)

/- Expensive coercion that can only appear at the beggining of a sequence of coercions. -/
class CoeHead (α : Sort u) (β : Sort v) :=
  (coe : α → β)

/- Expensive coercion that can only appear at the end of a sequence of coercions. -/
class CoeTail (α : Sort u) (β : Sort v) :=
  (coe : α → β)

class CoeDep (α : Sort u) (a : α) (β : Sort v) :=
  (coe : β)

/- Combines CoeHead, CoeTC, CoeTail, CoeDep -/
class CoeT (α : Sort u) (a : α) (β : Sort v) :=
  (coe : β)

class CoeFun (α : Sort u) (γ : outParam (α → outParam (Sort v))) :=
  (coe : (a : α) → γ a)

class CoeSort (α : Sort u) (β : outParam (Sort v)) :=
  (coe : α → β)

abbrev coeB {α : Sort u} {β : Sort v} [Coe α β] (a : α) : β :=
  Coe.coe a

abbrev coeHead {α : Sort u} {β : Sort v} [CoeHead α β] (a : α) : β :=
  CoeHead.coe a

abbrev coeTail {α : Sort u} {β : Sort v} [CoeTail α β] (a : α) : β :=
  CoeTail.coe a

abbrev coeD {α : Sort u} {β : Sort v} (a : α) [CoeDep α a β] : β :=
  CoeDep.coe a

abbrev coeTC {α : Sort u} {β : Sort v} [CoeTC α β] (a : α) : β :=
  CoeTC.coe a

/-- Apply coercion manually. -/
abbrev coe {α : Sort u} {β : Sort v} (a : α) [CoeT α a β] : β :=
  CoeT.coe a

abbrev coeFun {α : Sort u} {γ : α → Sort v} (a : α) [CoeFun α γ] : γ a :=
  CoeFun.coe a

abbrev coeSort {α : Sort u} {β : Sort v} (a : α) [CoeSort α β] : β :=
  CoeSort.coe a

instance coeTrans {α : Sort u} {β : Sort v} {δ : Sort w} [CoeTC α β] [Coe β δ] : CoeTC α δ := {
  coe := fun a => coeB (coeTC a : β)
}

instance coeBase {α : Sort u} {β : Sort v} [Coe α β] : CoeTC α β := {
  coe := fun a => coeB a
}

instance coeOfHeafOfTCOfTail {α : Sort u} {β : Sort v} {δ : Sort w} {γ : Sort w'} (a : α) [CoeTC β δ] [CoeTail δ γ] [CoeHead α β] : CoeT α a γ := {
  coe := coeTail (coeTC (coeHead a : β) : δ)
}

instance coeOfHeadOfTC {α : Sort u} {β : Sort v} {δ : Sort w} (a : α) [CoeTC β δ] [CoeHead α β] : CoeT α a δ  := {
  coe := coeTC (coeHead a : β)
}

instance coeOfTCOfTail {α : Sort u} {β : Sort v} {δ : Sort w} (a : α) [CoeTC α β] [CoeTail β δ] : CoeT α a δ := {
  coe := coeTail (coeTC a : β)
}

instance coeOfHead {α : Sort u} {β : Sort v} (a : α) [CoeHead α β] : CoeT α a β := {
  coe := coeHead a
}

instance coeOfTail {α : Sort u} {β : Sort v} (a : α) [CoeTail α β] : CoeT α a β := {
  coe := coeTail a
}

instance coeOfTC {α : Sort u} {β : Sort v} (a : α) [CoeTC α β] : CoeT α a β := {
  coe := coeTC a
}

instance coeOfDep {α : Sort u} {β : Sort v} (a : α) [CoeDep α a β] : CoeT α a β := {
  coe := coeD a
}

instance coeId {α : Sort u} (a : α) : CoeT α a α := {
  coe := a
}

instance coeFunTrans {α : Sort u} {β : Sort v} {γ : β → Sort w} [CoeFun β γ] [Coe α β] : CoeFun α (fun a => γ (coe a)) := {
  coe := fun a => coeFun (coeB a : β)
}

instance coeSortTrans {α : Sort u} {β : Sort v} {δ : Sort w} [CoeSort β δ] [Coe α β] : CoeSort α δ := {
  coe := fun a => coeSort (coeB a : β)
}

/- Basic instances -/

@[inline] instance boolToProp : Coe Bool Prop := {
  coe := fun b => b = true
}

@[inline] instance coeDecidableEq (x : Bool) : Decidable (coe x) :=
inferInstanceAs (Decidable (x = true))

instance decPropToBool (p : Prop) [Decidable p] : CoeDep Prop p Bool := {
  coe := decide p
}

instance optionCoe {α : Type u} : CoeTail α (Option α) := {
  coe := some
}

instance subtypeCoe {α : Sort u} {p : α → Prop} : CoeHead { x // p x } α := {
  coe := fun v => v.val
}

/- Coe & OfNat bridge -/

/-
  Remark: one may question why we use `OfNat α` instead of `Coe Nat α`.
  Reason: `OfNat` is for implementing polymorphic numeric literals, and we may
  want to have numberic literals for a type α and **no** coercion from `Nat` to `α`. -/
instance hasOfNatOfCoe {α : Type u} {β : Type v} [OfNat α] [Coe α β] : OfNat β := {
  ofNat := fun (n : Nat) => coe (OfNat.ofNat n : α)
}

@[inline] def liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u} [MonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β := do
  let a ← liftM x
  pure (coe a)

@[inline] def coeM {m : Type u → Type v} {α β : Type u} [∀ a, CoeT α a β] [Monad m] (x : m α) : m β := do
  let a ← x
  pure $ coe a
