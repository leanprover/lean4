/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Std.Data.HashSet
import Std.Data.RBMap
import Std.Data.RBTree
import Lean.Data.SSet
namespace Lean

instance : Coe String Name := ⟨Name.mkSimple⟩

namespace Name
-- Remark: we export the `Name.hash` to make sure it matches the hash implemented in C++
@[export lean_name_hash_exported] def hashEx : Name → UInt64 :=
  Name.hash

def getPrefix : Name → Name
  | anonymous => anonymous
  | str p _   => p
  | num p _   => p

def getString! : Name → String
  | str _ s => s
  | _       => unreachable!

def getNumParts : Name → Nat
  | anonymous => 0
  | str p _   => getNumParts p + 1
  | num p _   => getNumParts p + 1

def updatePrefix : Name → Name → Name
  | anonymous, _    => anonymous
  | str _ s,   newP => Name.mkStr newP s
  | num _ s,   newP => Name.mkNum newP s

def components' : Name → List Name
  | anonymous => []
  | str n s   => Name.mkStr anonymous s :: components' n
  | num n v   => Name.mkNum anonymous v :: components' n

def components (n : Name) : List Name :=
  n.components'.reverse

def eqStr : Name → String → Bool
  | str anonymous s, s' => s == s'
  | _,                 _  => false

def isPrefixOf : Name → Name → Bool
  | p, anonymous    => p == anonymous
  | p, n@(num p' _) => p == n || isPrefixOf p p'
  | p, n@(str p' _) => p == n || isPrefixOf p p'


def isSuffixOf : Name → Name → Bool
  | anonymous, _         => true
  | str p₁ s₁, str p₂ s₂ => s₁ == s₂ && isSuffixOf p₁ p₂
  | num p₁ n₁, num p₂ n₂ => n₁ == n₂ && isSuffixOf p₁ p₂
  | _,         _         => false

def cmp : Name → Name → Ordering
  | anonymous, anonymous => Ordering.eq
  | anonymous, _         => Ordering.lt
  | _,         anonymous => Ordering.gt
  | num p₁ i₁, num p₂ i₂ =>
    match cmp p₁ p₂ with
    | Ordering.eq => compare i₁ i₂
    | ord => ord
  | num _ _,   str _ _   => Ordering.lt
  | str _ _,   num _ _   => Ordering.gt
  | str p₁ n₁, str p₂ n₂ =>
    match cmp p₁ p₂ with
    | Ordering.eq => compare n₁ n₂
    | ord => ord

def lt (x y : Name) : Bool :=
  cmp x y == Ordering.lt

def quickCmpAux : Name → Name → Ordering
  | anonymous, anonymous => Ordering.eq
  | anonymous, _         => Ordering.lt
  | _,         anonymous => Ordering.gt
  | num n v, num n' v' =>
    match compare v v' with
    | Ordering.eq => n.quickCmpAux n'
    | ord => ord
  | num _ _, str _  _  => Ordering.lt
  | str _ _, num _  _  => Ordering.gt
  | str n s, str n' s' =>
    match compare s s' with
    | Ordering.eq => n.quickCmpAux n'
    | ord => ord

def quickCmp (n₁ n₂ : Name) : Ordering :=
  match compare n₁.hash n₂.hash with
  | Ordering.eq => quickCmpAux n₁ n₂
  | ord => ord

def quickLt (n₁ n₂ : Name) : Bool :=
  quickCmp n₁ n₂ == Ordering.lt

/-- Alternative HasLt instance. -/
@[inline] protected def hasLtQuick : LT Name :=
  ⟨fun a b => Name.quickLt a b = true⟩

@[inline] instance : DecidableRel (@LT.lt Name Name.hasLtQuick) :=
  inferInstanceAs (DecidableRel (fun a b => Name.quickLt a b = true))

/-- The frontend does not allow user declarations to start with `_` in any of its parts.
   We use name parts starting with `_` internally to create auxiliary names (e.g., `_private`). -/
def isInternal : Name → Bool
  | str p s => s.get 0 == '_' || isInternal p
  | num p _ => isInternal p
  | _       => false

def isAtomic : Name → Bool
  | anonymous       => true
  | str anonymous _ => true
  | num anonymous _ => true
  | _               => false

def isAnonymous : Name → Bool
  | anonymous         => true
  | _                 => false

def isStr : Name → Bool
  | str .. => true
  | _      => false

def isNum : Name → Bool
  | num .. => true
  | _      => false

end Name

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

open Lean

def String.toName (s : String) : Name :=
  let ps := s.splitOn ".";
  ps.foldl (fun n p => Name.mkStr n p.trim) Name.anonymous
