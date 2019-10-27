/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.PersistentHashMap

universes u v

structure PersistentHashSet (α : Type u) [HasBeq α] [Hashable α] :=
(set : PersistentHashMap α Unit)

abbrev PHashSet (α : Type u) [HasBeq α] [Hashable α] := PersistentHashSet α

namespace PersistentHashSet

variables {α : Type u} [HasBeq α] [Hashable α]

@[inline] def isEmpty (s : PersistentHashSet α) : Bool :=
s.set.isEmpty

@[inline] def empty : PersistentHashSet α :=
{ set := PersistentHashMap.empty }

instance : Inhabited (PersistentHashSet α) :=
⟨empty⟩

instance : HasEmptyc (PersistentHashSet α) :=
⟨empty⟩

@[inline] def insert (s : PersistentHashSet α) (a : α) : PersistentHashSet α :=
{ set := s.set.insert a () }

@[inline] def erase (s : PersistentHashSet α) (a : α) : PersistentHashSet α :=
{ set := s.set.erase a }

@[inline] def contains (s : PersistentHashSet α) (a : α) : Bool :=
s.set.contains a

@[inline] def size (s : PersistentHashSet α) : Nat :=
s.set.size

@[inline] def mfold {β : Type v} {m : Type v → Type v} [Monad m] (f : β → α → m β) (d : β) (s : PersistentHashSet α) : m β :=
s.set.mfoldl (fun d a _ => f d a) d

@[inline] def fold {β : Type v} (f : β → α → β) (d : β) (s : PersistentHashSet α) : β :=
Id.run $ s.mfold f d

end PersistentHashSet
