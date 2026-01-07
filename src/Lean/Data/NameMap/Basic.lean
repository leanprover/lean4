/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Std.Data.HashSet.Basic
public import Std.Data.TreeSet.Basic
public import Lean.Data.SSet
public import Lean.Data.Name

public section

namespace Lean

@[expose] def NameMap (α : Type) := Std.TreeMap Name α Name.quickCmp

@[inline] def mkNameMap (α : Type) : NameMap α := Std.TreeMap.empty

namespace NameMap
variable {α : Type}

instance [Repr α] : Repr (NameMap α) := inferInstanceAs (Repr (Std.TreeMap _ _ _))

instance (α : Type) : EmptyCollection (NameMap α) := ⟨mkNameMap α⟩

instance (α : Type) : Inhabited (NameMap α) where
  default := {}

def insert (m : NameMap α) (n : Name) (a : α) := Std.TreeMap.insert m n a

def contains (m : NameMap α) (n : Name) : Bool := Std.TreeMap.contains m n

def find? (m : NameMap α) (n : Name) : Option α := Std.TreeMap.get? m n

instance [Monad m] : ForIn m (NameMap α) (Name × α) :=
  inferInstanceAs (ForIn _ (Std.TreeMap _ _ _) ..)

/-- `filter f m` returns the `NameMap` consisting of all
"`key`/`val`"-pairs in `m` where `f key val` returns `true`. -/
def filter (f : Name → α → Bool) (m : NameMap α) : NameMap α := Std.TreeMap.filter f m

end NameMap

@[expose] def NameSet := Std.TreeSet Name Name.quickCmp

namespace NameSet
def empty : NameSet := Std.TreeSet.empty
instance : EmptyCollection NameSet := ⟨empty⟩
instance : Inhabited NameSet := ⟨empty⟩
def insert (s : NameSet) (n : Name) : NameSet := Std.TreeSet.insert s n
def contains (s : NameSet) (n : Name) : Bool := Std.TreeSet.contains s n
instance : Membership Name NameSet := ⟨fun (s : NameSet) (n : Name) => s.contains n = true⟩
instance [Monad m] : ForIn m NameSet Name :=
  inferInstanceAs (ForIn _ (Std.TreeSet _ _) ..)

/-- The union of two `NameSet`s. -/
def append (s t : NameSet) : NameSet :=
  s.merge t

instance : Append NameSet where
  append := NameSet.append

instance : Singleton Name NameSet where
  singleton := fun n => (∅ : NameSet).insert n

instance : Union NameSet where
  union := NameSet.append

instance : Inter NameSet where
  inter := fun s t => s.foldl (fun r n => if t.contains n then r.insert n else r) {}

instance : SDiff NameSet where
  sdiff := fun s t => t.foldl (fun s n => s.erase n) s

/-- `filter f s` returns the `NameSet` consisting of all `x` in `s` where `f x` returns `true`. -/
def filter (f : Name → Bool) (s : NameSet) : NameSet := Std.TreeSet.filter f s

def ofList (l : List Name) : NameSet := Std.TreeSet.ofList l _

def ofArray (l : Array Name) : NameSet := Std.TreeSet.ofArray l _

end NameSet

@[expose] def NameSSet := SSet Name

namespace NameSSet
abbrev empty : NameSSet := SSet.empty
instance : EmptyCollection NameSSet := ⟨empty⟩
instance : Inhabited NameSSet := ⟨empty⟩
abbrev insert (s : NameSSet) (n : Name) : NameSSet := SSet.insert s n
abbrev contains (s : NameSSet) (n : Name) : Bool := SSet.contains s n
instance : Membership Name NameSSet := ⟨fun (s : NameSSet) (n : Name) => s.contains n = true⟩
instance [Monad m] : ForIn m NameSSet Name := inferInstanceAs (ForIn _ (SSet _) ..)
end NameSSet

@[expose] def NameHashSet := Std.HashSet Name

namespace NameHashSet
@[inline] def empty : NameHashSet := (∅ : Std.HashSet Name)
instance : EmptyCollection NameHashSet := ⟨empty⟩
instance : Inhabited NameHashSet := ⟨{}⟩
def insert (s : NameHashSet) (n : Name) := Std.HashSet.insert s n
def contains (s : NameHashSet) (n : Name) : Bool := Std.HashSet.contains s n
instance : Membership Name NameHashSet := ⟨fun (s : NameHashSet) (n : Name) => s.contains n = true⟩

/-- `filter f s` returns the `NameHashSet` consisting of all `x` in `s` where `f x` returns `true`. -/
def filter (f : Name → Bool) (s : NameHashSet) : NameHashSet := Std.HashSet.filter f s

/-- The union of two `NameHashSet`s. -/
def append (s t : NameHashSet) : NameHashSet :=
  t.fold (init := s) fun s n => s.insert n

instance : Append NameHashSet := ⟨NameHashSet.append⟩

instance : Singleton Name NameHashSet where
  singleton := fun n => (∅ : NameHashSet).insert n

instance : Union NameHashSet where
  union := NameHashSet.append

end NameHashSet

def MacroScopesView.isPrefixOf (v₁ v₂ : MacroScopesView) : Bool :=
  v₁.name.isPrefixOf v₂.name &&
  v₁.scopes == v₂.scopes &&
  v₁.ctx == v₂.ctx &&
  v₁.imported == v₂.imported

def MacroScopesView.isSuffixOf (v₁ v₂ : MacroScopesView) : Bool :=
  v₁.name.isSuffixOf v₂.name &&
  v₁.scopes == v₂.scopes &&
  v₁.ctx == v₂.ctx &&
  v₁.imported == v₂.imported

end Lean
