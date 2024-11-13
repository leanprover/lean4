/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Std.Data.HashSet.Basic
import Lean.Data.HashSet
import Lean.Data.RBMap
import Lean.Data.RBTree
import Lean.Data.SSet
import Lean.Data.Name
namespace Lean

def NameMap (α : Type) := RBMap Name α Name.quickCmp

@[inline] def mkNameMap (α : Type) : NameMap α := mkRBMap Name α Name.quickCmp

namespace NameMap
variable {α : Type}

instance (α : Type) : EmptyCollection (NameMap α) := ⟨mkNameMap α⟩

instance (α : Type) : Inhabited (NameMap α) where
  default := {}

def insert (m : NameMap α) (n : Name) (a : α) := RBMap.insert m n a

def contains (m : NameMap α) (n : Name) : Bool := RBMap.contains m n

def find? (m : NameMap α) (n : Name) : Option α := RBMap.find? m n

instance : ForIn m (NameMap α) (Name × α) :=
  inferInstanceAs (ForIn _ (RBMap ..) ..)

/-- `filter f m` returns the `NameMap` consisting of all
"`key`/`val`"-pairs in `m` where `f key val` returns `true`. -/
def filter (f : Name → α → Bool) (m : NameMap α) : NameMap α := RBMap.filter f m

/-- `filterMap f m` filters an `NameMap` and simultaneously modifies the filtered values.

It takes a function `f : Name → α → Option β` and applies `f name` to the value with key `name`.
The resulting entries with non-`none` value are collected to form the output `NameMap`. -/
def filterMap (f : Name → α → Option β) (m : NameMap α) : NameMap β := RBMap.filterMap f m

end NameMap

def NameSet := RBTree Name Name.quickCmp

namespace NameSet
def empty : NameSet := mkRBTree Name Name.quickCmp
instance : EmptyCollection NameSet := ⟨empty⟩
instance : Inhabited NameSet := ⟨empty⟩
def insert (s : NameSet) (n : Name) : NameSet := RBTree.insert s n
def contains (s : NameSet) (n : Name) : Bool := RBMap.contains s n
instance : ForIn m NameSet Name :=
  inferInstanceAs (ForIn _ (RBTree ..) ..)

/-- The union of two `NameSet`s. -/
def append (s t : NameSet) : NameSet :=
  s.mergeBy (fun _ _ _ => .unit) t

instance : Append NameSet where
  append := NameSet.append

/-- `filter f s` returns the `NameSet` consisting of all `x` in `s` where `f x` returns `true`. -/
def filter (f : Name → Bool) (s : NameSet) : NameSet := RBTree.filter f s

end NameSet

def NameSSet := SSet Name

namespace NameSSet
abbrev empty : NameSSet := SSet.empty
instance : EmptyCollection NameSSet := ⟨empty⟩
instance : Inhabited NameSSet := ⟨empty⟩
abbrev insert (s : NameSSet) (n : Name) : NameSSet := SSet.insert s n
abbrev contains (s : NameSSet) (n : Name) : Bool := SSet.contains s n
end NameSSet

def NameHashSet := Std.HashSet Name

namespace NameHashSet
@[inline] def empty : NameHashSet := Std.HashSet.empty
instance : EmptyCollection NameHashSet := ⟨empty⟩
instance : Inhabited NameHashSet := ⟨{}⟩
def insert (s : NameHashSet) (n : Name) := Std.HashSet.insert s n
def contains (s : NameHashSet) (n : Name) : Bool := Std.HashSet.contains s n

/-- `filter f s` returns the `NameHashSet` consisting of all `x` in `s` where `f x` returns `true`. -/
def filter (f : Name → Bool) (s : NameHashSet) : NameHashSet := Std.HashSet.filter f s
end NameHashSet

def MacroScopesView.isPrefixOf (v₁ v₂ : MacroScopesView) : Bool :=
  v₁.name.isPrefixOf v₂.name &&
  v₁.scopes == v₂.scopes &&
  v₁.mainModule == v₂.mainModule &&
  v₁.imported == v₂.imported

def MacroScopesView.isSuffixOf (v₁ v₂ : MacroScopesView) : Bool :=
  v₁.name.isSuffixOf v₂.name &&
  v₁.scopes == v₂.scopes &&
  v₁.mainModule == v₂.mainModule &&
  v₁.imported == v₂.imported

end Lean
