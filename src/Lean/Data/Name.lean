/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Std.Data.HashSet
import Std.Data.RBMap
import Std.Data.RBTree
namespace Lean

instance : Coe String Name := ⟨Name.mkSimple⟩

namespace Name

@[export lean_name_hash] def hashEx : Name → USize :=
  Name.hash

def getPrefix : Name → Name
  | anonymous => anonymous
  | str p s _ => p
  | num p s _ => p

def getRoot : Name → Name
  | anonymous             => anonymous
  | n@(str anonymous _ _) => n
  | n@(num anonymous _ _) => n
  | str n _ _             => getRoot n
  | num n _ _             => getRoot n

def getString! : Name → String
  | str _ s _ => s
  | _         => unreachable!

def getNumParts : Name → Nat
  | anonymous => 0
  | str p _ _ => getNumParts p + 1
  | num p _ _ => getNumParts p + 1

def updatePrefix : Name → Name → Name
  | anonymous, newP => anonymous
  | str p s _, newP => Name.mkStr newP s
  | num p s _, newP => Name.mkNum newP s

def components' : Name → List Name
  | anonymous => []
  | str n s _ => Name.mkStr anonymous s :: components' n
  | num n v _ => Name.mkNum anonymous v :: components' n

def components (n : Name) : List Name :=
  n.components'.reverse

def eqStr : Name → String → Bool
  | str anonymous s _, s' => s == s'
  | _,                 _  => false

def isPrefixOf : Name → Name → Bool
  | p, anonymous      => p == anonymous
  | p, n@(num p' _ _) => p == n || isPrefixOf p p'
  | p, n@(str p' _ _) => p == n || isPrefixOf p p'


def isSuffixOf : Name → Name → Bool
  | anonymous,   _           => true
  | str p₁ s₁ _, str p₂ s₂ _ => s₁ == s₂ && isSuffixOf p₁ p₂
  | num p₁ n₁ _, num p₂ n₂ _ => n₁ == n₂ && isSuffixOf p₁ p₂
  | _,           _           => false

def lt : Name → Name → Bool
  | anonymous,   anonymous   => false
  | anonymous,   _           => true
  | num p₁ i₁ _, num p₂ i₂ _ => lt p₁ p₂ || (p₁ == p₂ && i₁ < i₂)
  | num _ _ _,   str _ _ _   => true
  | str p₁ n₁ _, str p₂ n₂ _ => lt p₁ p₂ || (p₁ == p₂ && n₁ < n₂)
  | _,           _           => false

def quickLtAux : Name → Name → Bool
  | anonymous, anonymous   => false
  | anonymous, _           => true
  | num n v _, num n' v' _ => v < v' || (v = v' && n.quickLtAux n')
  | num _ _ _, str _ _ _   => true
  | str n s _, str n' s' _ => s < s' || (s = s' && n.quickLtAux n')
  | _,         _           => false

def quickLt (n₁ n₂ : Name) : Bool :=
  if n₁.hash < n₂.hash then true
  else if n₁.hash > n₂.hash then false
  else quickLtAux n₁ n₂

/- Alternative HasLt instance. -/
@[inline] protected def hasLtQuick : HasLess Name :=
  ⟨fun a b => Name.quickLt a b = true⟩

@[inline] instance : DecidableRel (@Less Name Name.hasLtQuick) :=
  inferInstanceAs (DecidableRel (fun a b => Name.quickLt a b = true))

/- The frontend does not allow user declarations to start with `_` in any of its parts.
   We use name parts starting with `_` internally to create auxiliary names (e.g., `_private`). -/
def isInternal : Name → Bool
  | str p s _ => s.get 0 == '_' || isInternal p
  | num p _ _ => isInternal p
  | _         => false

def isAtomic : Name → Bool
  | anonymous         => true
  | str anonymous _ _ => true
  | num anonymous _ _ => true
  | _                 => false

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

def NameMap (α : Type) := Std.RBMap Name α Name.quickLt

@[inline] def mkNameMap (α : Type) : NameMap α := Std.mkRBMap Name α Name.quickLt

namespace NameMap
variable {α : Type}

instance (α : Type) : EmptyCollection (NameMap α) := ⟨mkNameMap α⟩

instance (α : Type) : Inhabited (NameMap α) where
  default := {}

def insert (m : NameMap α) (n : Name) (a : α) := Std.RBMap.insert m n a

def contains (m : NameMap α) (n : Name) : Bool := Std.RBMap.contains m n

@[inline] def find? (m : NameMap α) (n : Name) : Option α := Std.RBMap.find? m n

end NameMap

def NameSet := RBTree Name Name.quickLt

namespace NameSet
def empty : NameSet := mkRBTree Name Name.quickLt
instance : EmptyCollection NameSet := ⟨empty⟩
instance : Inhabited NameSet := ⟨{}⟩
def insert (s : NameSet) (n : Name) : NameSet := Std.RBTree.insert s n
def contains (s : NameSet) (n : Name) : Bool := Std.RBMap.contains s n
instance : ForIn m NameSet Name :=
  inferInstanceAs (ForIn _ (Std.RBTree ..) ..)

end NameSet

def NameHashSet := Std.HashSet Name

namespace NameHashSet
@[inline] def empty : NameHashSet := Std.HashSet.empty
instance : EmptyCollection NameHashSet := ⟨empty⟩
instance : Inhabited NameHashSet := ⟨{}⟩
def insert (s : NameHashSet) (n : Name) := Std.HashSet.insert s n
def contains (s : NameHashSet) (n : Name) : Bool := Std.HashSet.contains s n
end NameHashSet

end Lean

open Lean

def String.toName (s : String) : Name :=
  let ps := s.splitOn ".";
  ps.foldl (fun n p => Name.mkStr n p.trim) Name.anonymous
