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

class CoeDep (α : Sort u) (_ : α) (β : Sort v) where
  coe : β

/- Combines CoeHead, CoeTC, CoeTail, CoeDep -/
class CoeT (α : Sort u) (_ : α) (β : Sort v) where
  coe : β

class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
  coe : (a : α) → γ a

class CoeSort (α : Sort u) (β : outParam (Sort v)) where
  coe : α → β

syntax:max (name := coeNotation) "↑" term:max : term

instance coeTrans {α : Sort u} {β : Sort v} {δ : Sort w} [Coe β δ] [CoeTC α β] : CoeTC α δ where
  coe a := Coe.coe (CoeTC.coe a : β)

instance coeBase {α : Sort u} {β : Sort v} [Coe α β] : CoeTC α β where
  coe a := Coe.coe a

instance coeOfHeafOfTCOfTail {α : Sort u} {β : Sort v} {δ : Sort w} {γ : Sort w'} [CoeHead α β] [CoeTail δ γ] [CoeTC β δ] : CoeHTCT α γ where
  coe a := CoeTail.coe (CoeTC.coe (CoeHead.coe a : β) : δ)

instance coeOfHeadOfTC {α : Sort u} {β : Sort v} {δ : Sort w} [CoeHead α β] [CoeTC β δ] : CoeHTCT α δ  where
  coe a := CoeTC.coe (CoeHead.coe a : β)

instance coeOfTCOfTail {α : Sort u} {β : Sort v} {δ : Sort w} [CoeTail β δ] [CoeTC α β] : CoeHTCT α δ where
  coe a := CoeTail.coe (CoeTC.coe a : β)

instance coeOfHead {α : Sort u} {β : Sort v} [CoeHead α β] : CoeHTCT α β where
  coe a := CoeHead.coe a

instance coeOfTail {α : Sort u} {β : Sort v} [CoeTail α β] : CoeHTCT α β where
  coe a := CoeTail.coe a

instance coeOfTC {α : Sort u} {β : Sort v} [CoeTC α β] : CoeHTCT α β where
  coe a := CoeTC.coe a

instance coeOfHTCT {α : Sort u} {β : Sort v} [CoeHTCT α β] (a : α) : CoeT α a β where
  coe := CoeHTCT.coe a

instance coeOfDep {α : Sort u} {β : Sort v} (a : α) [CoeDep α a β] : CoeT α a β where
  coe := CoeDep.coe a

instance coeId {α : Sort u} (a : α) : CoeT α a α where
  coe := a

instance coeSortToCoeTail [inst : CoeSort α β] : CoeTail α β where
  coe := inst.coe

/- Basic instances -/

@[inline] instance boolToProp : Coe Bool Prop where
  coe b := b = true

instance boolToSort : CoeSort Bool Prop where
  coe b := b = true

instance decPropToBool (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p

instance optionCoe {α : Type u} : CoeTail α (Option α) where
  coe := some

instance subtypeCoe {α : Sort u} {p : α → Prop} : CoeHead { x // p x } α where
  coe v := v.val

/- Coe bridge -/

-- Helper definition used by the elaborator. It is not meant to be used directly by users
@[inline] def Lean.Internal.liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u} [MonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β := do
  let a ← liftM x
  pure (CoeT.coe a)

-- Helper definition used by the elaborator. It is not meant to be used directly by users
@[inline] def Lean.Internal.coeM {m : Type u → Type v} {α β : Type u} [∀ a, CoeT α a β] [Monad m] (x : m α) : m β := do
  let a ← x
  pure <| CoeT.coe a

instance [CoeFun α β] (a : α) : CoeDep α a (β a) where
  coe := CoeFun.coe a

instance [CoeFun α (fun _ => β)] : CoeTail α β  where
  coe a := CoeFun.coe a

instance [CoeSort α β] : CoeTail α β where
  coe a := CoeSort.coe a
