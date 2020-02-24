/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.HashMap

universes u v

structure HashSet (α : Type u) [HasBeq α] [Hashable α] :=
(set : HashMap α Unit)

def mkHashSet {α : Type u} [HasBeq α] [Hashable α] (nbuckets := 8) : HashSet α :=
{ set := mkHashMap nbuckets }

namespace HashSet

variables {α : Type u} [HasBeq α] [Hashable α]

instance : Inhabited (HashSet α) :=
⟨mkHashSet⟩

instance : HasEmptyc (HashSet α) :=
⟨mkHashSet⟩

@[inline] def insert (s : HashSet α) (a : α) : HashSet α :=
{ set := s.set.insert a () }

@[inline] def erase (s : HashSet α) (a : α) : HashSet α :=
{ set := s.set.erase a }

@[inline] def find? (s : HashSet α) (a : α) : Option α :=
match s.set.findEntry? a with
| some (k, _) => some k
| none        => none

@[inline] def contains (s : HashSet α) (a : α) : Bool :=
s.set.contains a

@[inline] def size (s : HashSet α) : Nat :=
s.set.size

@[inline] def isEmpty (s : HashSet α) : Bool :=
s.set.isEmpty

@[inline] def empty : HashSet α :=
mkHashSet

@[inline] def foldM {β : Type v} {m : Type v → Type v} [Monad m] (f : β → α → m β) (d : β) (s : HashSet α) : m β :=
s.set.foldM (fun d a _ => f d a) d

@[inline] def fold {β : Type v} (f : β → α → β) (d : β) (s : HashSet α) : β :=
Id.run $ s.foldM f d

end HashSet
