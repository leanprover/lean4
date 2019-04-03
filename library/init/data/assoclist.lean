/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.core
universes u v w

/- List-like type to avoid extra level of indirection -/
inductive AssocList (α : Type u) (β : Type v)
| nil {} : AssocList
| cons (key : α) (value : β) (tail : AssocList) : AssocList

namespace AssocList
variables {α : Type u} {β : Type v} {δ : Type w}

@[specialize] def foldl (f : δ → α → β → δ) : δ → AssocList α β → δ
| d nil           := d
| d (cons a b es) := foldl (f d a b) es

def find [HasBeq α] (a : α) : AssocList α β → Option β
| nil           := none
| (cons k v es) := match k == a with
  | true  := some v
  | false := find es

def contains [HasBeq α] (a : α) : AssocList α β → Bool
| nil           := false
| (cons k v es) := k == a || contains es

def replace [HasBeq α] (a : α) (b : β) : AssocList α β → AssocList α β
| nil           := nil
| (cons k v es) := match k == a with
  | true  := cons a b es
  | false := cons k v (replace es)

def erase [HasBeq α] (a : α) : AssocList α β → AssocList α β
| nil           := nil
| (cons k v es) := match k == a with
  | true  := es
  | false := cons k v (erase es)

end AssocList
