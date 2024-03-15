/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.Id
import Init.Data.List.Basic
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

/-- Auxiliary for `List.reverse`. `List.reverseAux l r = l.reverse ++ r`, but it is defined directly. -/
def reverseAux : AssocList α β → AssocList α β → AssocList α β
  | nil,   r => r
  | cons k v l, r => reverseAux l (cons k v r)

def reverse (as : AssocList α β) : AssocList α β := reverseAux as nil

@[inline]
def mapValM {m : Type u → Type v} [Monad m] {α : Type u} {β γ : Type _} (f : β → m γ) (as : AssocList α β) : m (AssocList α γ) :=
  let rec @[specialize] loop
    | nil,         bs => pure bs.reverse
    | cons k v as, bs => do loop as (cons k (← f v) bs)
  loop as nil

def getEntry? [BEq α] (a : α) : AssocList α β → Option (α × β)
  | nil         => none
  | cons k v es => match k == a with
    | true  => some (k, v)
    | false => getEntry? a es

def get? [BEq α] (a : α) : AssocList α β → Option β
  | nil         => none
  | cons k v es => match k == a with
    | true  => some v
    | false => get? a es

@[deprecated getEntry?] def findEntry? [BEq α] : α → AssocList α β → Option (α × β) := getEntry?
@[deprecated getEntry?] def find? [BEq α] : α → AssocList α β → Option β := get?

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
