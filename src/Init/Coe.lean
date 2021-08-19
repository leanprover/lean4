/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core

universe u v w w'

class Coe (α : Sort u) (β : Sort v) where
  coe : α → β

/-- Auxiliary class that contains the transitive closure of `Coe`. -/
class CoeTC (α : Sort u) (β : Sort v) where
  coe : α → β

/- Expensive coercion that can only appear at the beginning of a sequence of coercions. -/
class CoeHead (α : Sort u) (β : Sort v) where
  coe : α → β

/- Expensive coercion that can only appear at the end of a sequence of coercions. -/
class CoeTail (α : Sort u) (β : Sort v) where
  coe : α → β

/-- Auxiliary class that contains `CoeHead` + `CoeTC` + `CoeTail`. -/
class CoeHTCT (α : Sort u) (β : Sort v) where
  coe : α → β

class CoeDep (α : Sort u) (a : α) (β : Sort v) where
  coe : β

/- Combines CoeHead, CoeTC, CoeTail, CoeDep -/
class CoeT (α : Sort u) (a : α) (β : Sort v) where
  coe : β

class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
  coe : (a : α) → γ a

class CoeSort (α : Sort u) (β : outParam (Sort v)) where
  coe : α → β

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

prefix:max "↑" => coe

abbrev coeFun {α : Sort u} {γ : α → Sort v} (a : α) [CoeFun α γ] : γ a :=
  CoeFun.coe a

abbrev coeSort {α : Sort u} {β : Sort v} (a : α) [CoeSort α β] : β :=
  CoeSort.coe a

instance coeTrans {α : Sort u} {β : Sort v} {δ : Sort w} [Coe β δ] [CoeTC α β] : CoeTC α δ where
  coe a := coeB (coeTC a : β)

instance coeBase {α : Sort u} {β : Sort v} [Coe α β] : CoeTC α β where
  coe a := coeB a

instance coeOfHeafOfTCOfTail {α : Sort u} {β : Sort v} {δ : Sort w} {γ : Sort w'} [CoeHead α β] [CoeTail δ γ] [CoeTC β δ] : CoeHTCT α γ where
  coe a := coeTail (coeTC (coeHead a : β) : δ)

instance coeOfHeadOfTC {α : Sort u} {β : Sort v} {δ : Sort w} [CoeHead α β] [CoeTC β δ] : CoeHTCT α δ  where
  coe a := coeTC (coeHead a : β)

instance coeOfTCOfTail {α : Sort u} {β : Sort v} {δ : Sort w} [CoeTail β δ] [CoeTC α β] : CoeHTCT α δ where
  coe a := coeTail (coeTC a : β)

instance coeOfHead {α : Sort u} {β : Sort v} [CoeHead α β] : CoeHTCT α β where
  coe a := coeHead a

instance coeOfTail {α : Sort u} {β : Sort v} [CoeTail α β] : CoeHTCT α β where
  coe a := coeTail a

instance coeOfTC {α : Sort u} {β : Sort v} [CoeTC α β] : CoeHTCT α β where
  coe a := coeTC a

instance coeOfHTCT {α : Sort u} {β : Sort v} [CoeHTCT α β] (a : α) : CoeT α a β where
  coe := CoeHTCT.coe a

instance coeOfDep {α : Sort u} {β : Sort v} (a : α) [CoeDep α a β] : CoeT α a β where
  coe := coeD a

instance coeId {α : Sort u} (a : α) : CoeT α a α where
  coe := a

instance coeSortToCoeTail [inst : CoeSort α β] : CoeTail α β where
  coe := inst.coe

/- Basic instances -/

@[inline] instance boolToProp : Coe Bool Prop where
  coe b := b = true

instance boolToSort : CoeSort Bool Prop where
  coe b := b

@[inline] instance coeDecidableEq (x : Bool) : Decidable (coe x) :=
  inferInstanceAs (Decidable (x = true))

instance decPropToBool (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p

instance optionCoe {α : Type u} : CoeTail α (Option α) where
  coe := some

instance subtypeCoe {α : Sort u} {p : α → Prop} : CoeHead { x // p x } α where
  coe v := v.val

/- Coe & OfNat bridge -/

/-
  Remark: one may question why we use `OfNat α` instead of `Coe Nat α`.
  Reason: `OfNat` is for implementing polymorphic numeric literals, and we may
  want to have numeric literals for a type α and **no** coercion from `Nat` to `α`. -/
instance hasOfNatOfCoe [Coe α β] [OfNat α n] : OfNat β n where
  ofNat := coe (OfNat.ofNat n : α)

@[inline] def liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u} [MonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β := do
  let a ← liftM x
  pure (coe a)

@[inline] def coeM {m : Type u → Type v} {α β : Type u} [∀ a, CoeT α a β] [Monad m] (x : m α) : m β := do
  let a ← x
  pure <| coe a

instance [CoeFun α β] (a : α) : CoeDep α a (β a) where
  coe := coeFun a

instance [CoeFun α (fun _ => β)] : CoeTail α β  where
  coe a := coeFun a

instance [CoeSort α β] : CoeTail α β where
  coe a := coeSort a
