/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Data.HashSet
import Lean.Data.RBMap
import Lean.Data.RBTree
import Lean.Data.SSet
import Lean.Data.Name
namespace Lean

instance : Coe String Name := ⟨Name.mkSimple⟩

open Std (RBMap RBTree mkRBMap mkRBTree)

def NameMap (α : Type) := Std.RBMap Name α Name.quickCmp

@[inline] def mkNameMap (α : Type) : NameMap α := Std.mkRBMap Name α Name.quickCmp

namespace NameMap
variable {α : Type}

instance (α : Type) : EmptyCollection (NameMap α) := ⟨mkNameMap α⟩

instance (α : Type) : Inhabited (NameMap α) where
  default := {}

def insert (m : NameMap α) (n : Name) (a : α) := Std.RBMap.insert m n a

def contains (m : NameMap α) (n : Name) : Bool := Std.RBMap.contains m n

@[inline] def find? (m : NameMap α) (n : Name) : Option α := Std.RBMap.find? m n

instance : ForIn m (NameMap α) (Name × α) :=
  inferInstanceAs (ForIn _ (Std.RBMap ..) ..)

end NameMap

def NameSet := RBTree Name Name.quickCmp

namespace NameSet
def empty : NameSet := mkRBTree Name Name.quickCmp
instance : EmptyCollection NameSet := ⟨empty⟩
instance : Inhabited NameSet := ⟨empty⟩
def insert (s : NameSet) (n : Name) : NameSet := Std.RBTree.insert s n
def contains (s : NameSet) (n : Name) : Bool := Std.RBMap.contains s n
instance : ForIn m NameSet Name :=
  inferInstanceAs (ForIn _ (Std.RBTree ..) ..)

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
