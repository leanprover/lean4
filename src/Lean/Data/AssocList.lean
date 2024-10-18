/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Id
import Init.Data.List.Impl

universe u v w w'
namespace Lean

/-- List-like type to avoid extra level of indirection -/
inductive AssocList (α : Type u) (β : Type v) where
  | nil : AssocList α β
  | cons (key : α) (value : β) (tail : AssocList α β) : AssocList α β
  deriving Inhabited

namespace AssocList
variable {α : Type u} {β : Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

abbrev empty : AssocList α β :=
  nil

instance : EmptyCollection (AssocList α β) := ⟨empty⟩

abbrev insert (m : AssocList α β) (k : α) (v : β) : AssocList α β :=
  m.cons k v

def isEmpty : AssocList α β → Bool
  | nil => true
  | _   => false

@[specialize] def foldlM (f : δ → α → β → m δ) : (init : δ) → AssocList α β → m δ
  | d, nil         => pure d
  | d, cons a b es => do
    let d ← f d a b
    foldlM f d es

@[inline] def foldl (f : δ → α → β → δ) (init : δ) (as : AssocList α β) : δ :=
  Id.run (foldlM f init as)

def toList (as : AssocList α β) : List (α × β) :=
  as.foldl (init := []) (fun r a b => (a, b)::r) |>.reverse

@[specialize] def forM (f : α → β → m PUnit) : AssocList α β → m PUnit
  | nil         => pure ⟨⟩
  | cons a b es => do f a b; forM f es

def mapKey (f : α → δ) : AssocList α β → AssocList δ β
  | nil        => nil
  | cons k v t => cons (f k) v (mapKey f t)

def mapVal (f : β → δ) : AssocList α β → AssocList α δ
  | nil        => nil
  | cons k v t => cons k (f v) (mapVal f t)

def findEntry? [BEq α] (a : α) : AssocList α β → Option (α × β)
  | nil         => none
  | cons k v es => match k == a with
    | true  => some (k, v)
    | false => findEntry? a es

def find? [BEq α] (a : α) : AssocList α β → Option β
  | nil         => none
  | cons k v es => match k == a with
    | true  => some v
    | false => find? a es

def contains [BEq α] (a : α) : AssocList α β → Bool
  | nil         => false
  | cons k _ es => k == a || contains a es

def replace [BEq α] (a : α) (b : β) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => match k == a with
    | true  => cons a b es
    | false => cons k v (replace a b es)

def erase [BEq α] (a : α) : AssocList α β → AssocList α β
  | nil         => nil
  | cons k v es => match k == a with
    | true  => es
    | false => cons k v (erase a es)

def any (p : α → β → Bool) : AssocList α β → Bool
  | nil         => false
  | cons k v es => p k v || any p es

def all (p : α → β → Bool) : AssocList α β → Bool
  | nil         => true
  | cons k v es => p k v && all p es

@[inline] protected def forIn {α : Type u} {β : Type v} {δ : Type w} {m : Type w → Type w'} [Monad m]
    (as : AssocList α β) (init : δ) (f : (α × β) → δ → m (ForInStep δ)) : m δ :=
  let rec @[specialize] loop
    | d, nil => pure d
    | d, cons k v es => do
      match (← f (k, v) d) with
      | ForInStep.done d  => pure d
      | ForInStep.yield d => loop d es
  loop init as

instance : ForIn m (AssocList α β) (α × β) where
  forIn := AssocList.forIn

end Lean.AssocList

def List.toAssocList' {α : Type u} {β : Type v} : List (α × β) → Lean.AssocList α β
  | []          => Lean.AssocList.nil
  | (a,b) :: es => Lean.AssocList.cons a b (toAssocList' es)
