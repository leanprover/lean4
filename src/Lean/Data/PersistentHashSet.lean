/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Lean.Data.PersistentHashMap

namespace Lean
universe u v

structure PersistentHashSet (α : Type u) [BEq α] [Hashable α] where
  (set : PersistentHashMap α Unit)

abbrev PHashSet (α : Type u) [BEq α] [Hashable α] := PersistentHashSet α

namespace PersistentHashSet

@[inline] def empty [BEq α] [Hashable α] : PersistentHashSet α :=
  { set := PersistentHashMap.empty }

instance [BEq α] [Hashable α] : Inhabited (PersistentHashSet α) where
  default := empty

instance [BEq α] [Hashable α] : EmptyCollection (PersistentHashSet α) :=
  ⟨empty⟩

variable {_ : BEq α} {_ : Hashable α}

@[inline] def insert (s : PersistentHashSet α) (a : α) : PersistentHashSet α :=
  { set := s.set.insert a () }

@[inline] def erase (s : PersistentHashSet α) (a : α) : PersistentHashSet α :=
  { set := s.set.erase a }

@[inline] def find? (s : PersistentHashSet α) (a : α) : Option α :=
  match s.set.findEntry? a with
  | some (a, _) => some a
  | none        => none

@[inline] def contains (s : PersistentHashSet α) (a : α) : Bool :=
  s.set.contains a

@[inline] def foldM {β : Type v} {m : Type v → Type v} [Monad m] (f : β → α → m β) (init : β) (s : PersistentHashSet α) : m β :=
  s.set.foldlM (init := init) fun d a _ => f d a

@[inline] def fold {β : Type v} (f : β → α → β) (init : β) (s : PersistentHashSet α) : β :=
  Id.run $ s.foldM f init

end PersistentHashSet

structure PersistentHashSetSized (α : Type u) [BEq α] [Hashable α] where
  (set : PersistentHashMapSized α Unit)

abbrev PHashSetSized (α : Type u) [BEq α] [Hashable α] := PersistentHashSetSized α

namespace PersistentHashSetSized

@[inline] def empty [BEq α] [Hashable α] : PersistentHashSetSized α :=
  { set := PersistentHashMapSized.empty }

instance [BEq α] [Hashable α] : Inhabited (PersistentHashSetSized α) where
  default := empty

instance [BEq α] [Hashable α] : EmptyCollection (PersistentHashSetSized α) :=
  ⟨empty⟩

variable {_ : BEq α} {_ : Hashable α}

@[inline] def isEmpty (s : PersistentHashSetSized α) : Bool :=
  s.set.isEmpty

@[inline] def insert (s : PersistentHashSetSized α) (a : α) : PersistentHashSetSized α :=
  { set := s.set.insert a () }

@[inline] def replace (s : PersistentHashSetSized α) (a : α) : PersistentHashSetSized α :=
  { set := s.set.replace a () }

@[inline] def insertNew (s : PersistentHashSetSized α) (a : α) : PersistentHashSetSized α :=
  { set := s.set.insertNew a () }

@[inline] def erase (s : PersistentHashSetSized α) (a : α) : PersistentHashSetSized α :=
  { set := s.set.erase a }

@[inline] def find? (s : PersistentHashSetSized α) (a : α) : Option α :=
  match s.set.findEntry? a with
  | some (a, _) => some a
  | none        => none

@[inline] def contains (s : PersistentHashSetSized α) (a : α) : Bool :=
  s.set.contains a

@[inline] def size (s : PersistentHashSetSized α) : Nat :=
  s.set.size

@[inline] def foldM {β : Type v} {m : Type v → Type v} [Monad m] (f : β → α → m β) (init : β) (s : PersistentHashSetSized α) : m β :=
  s.set.foldlM (init := init) fun d a _ => f d a

@[inline] def fold {β : Type v} (f : β → α → β) (init : β) (s : PersistentHashSetSized α) : β :=
  Id.run $ s.foldM f init
