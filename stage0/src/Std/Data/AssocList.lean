/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
namespace Std
universes u v w

/- List-like type to avoid extra level of indirection -/
inductive AssocList (α : Type u) (β : Type v)
| nil : AssocList
| cons (key : α) (value : β) (tail : AssocList) : AssocList

namespace AssocList
variables {α : Type u} {β : Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

abbrev empty : AssocList α β :=
nil

instance : HasEmptyc (AssocList α β) := ⟨empty⟩

abbrev insert (m : AssocList α β) (k : α) (v : β) : AssocList α β :=
m.cons k v

def isEmpty : AssocList α β → Bool
| nil => true
| _   => false

@[specialize] def foldlM (f : δ → α → β → m δ) : δ → AssocList α β → m δ
| d, nil         => pure d
| d, cons a b es => do d ← f d a b; foldlM d es

@[inline] def foldl (f : δ → α → β → δ) (d : δ) (as : AssocList α β) : δ :=
Id.run (foldlM f d as)

def mapKey (f : α → δ) : AssocList α β → AssocList δ β
| nil        => nil
| cons k v t => cons (f k) v (mapKey t)

def mapVal (f : β → δ) : AssocList α β → AssocList α δ
| nil        => nil
| cons k v t => cons k (f v) (mapVal t)

def findEntry? [HasBeq α] (a : α) : AssocList α β → Option (α × β)
| nil         => none
| cons k v es => match k == a with
  | true  => some (k, v)
  | false => findEntry? es

def find? [HasBeq α] (a : α) : AssocList α β → Option β
| nil         => none
| cons k v es => match k == a with
  | true  => some v
  | false => find? es

def contains [HasBeq α] (a : α) : AssocList α β → Bool
| nil         => false
| cons k v es => k == a || contains es

def replace [HasBeq α] (a : α) (b : β) : AssocList α β → AssocList α β
| nil         => nil
| cons k v es => match k == a with
  | true  => cons a b es
  | false => cons k v (replace es)

def erase [HasBeq α] (a : α) : AssocList α β → AssocList α β
| nil         => nil
| cons k v es => match k == a with
  | true  => es
  | false => cons k v (erase es)

def any (p : α → β → Bool) : AssocList α β → Bool
| nil         => false
| cons k v es => p k v || any es

def all (p : α → β → Bool) : AssocList α β → Bool
| nil         => true
| cons k v es => p k v && all es

end AssocList
end Std
