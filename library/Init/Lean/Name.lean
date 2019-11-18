/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Coe
import Init.Data.UInt
import Init.Data.ToString
import Init.Data.Hashable
import Init.Data.RBMap
import Init.Data.RBTree
namespace Lean

inductive Name
| anonymous : Name
| mkString  : Name → String → Name
| mkNumeral : Name → Nat → Name

attribute [extern "lean_name_mk_string"] Name.mkString
attribute [extern "lean_name_mk_numeral"] Name.mkNumeral

instance : Inhabited Name :=
⟨Name.anonymous⟩

def mkStrName (p : Name) (s : String) : Name :=
Name.mkString p s

def mkNumName (p : Name) (v : Nat) : Name :=
Name.mkNumeral p v

def mkSimpleName (s : String) : Name :=
mkStrName Name.anonymous s

instance stringToName : HasCoe String Name :=
⟨mkSimpleName⟩

namespace Name
@[extern "lean_name_hash_usize"]
constant hash (n : @& Name) : USize := arbitrary _

instance : Hashable Name :=
⟨Name.hash⟩

def getPrefix : Name → Name
| anonymous     => anonymous
| mkString p s  => p
| mkNumeral p s => p

def getNumParts : Name → Nat
| anonymous     => 0
| mkString p _  => getNumParts p + 1
| mkNumeral p _ => getNumParts p + 1

def updatePrefix : Name → Name → Name
| anonymous,     newP => anonymous
| mkString p s,  newP => mkString newP s
| mkNumeral p s, newP => mkNumeral newP s

def components' : Name → List Name
| anonymous     => []
| mkString n s  => mkString anonymous s :: components' n
| mkNumeral n v => mkNumeral anonymous v :: components' n

def components (n : Name) : List Name :=
n.components'.reverse

@[extern "lean_name_dec_eq"]
protected def decEq : ∀ (a b : @& Name), Decidable (a = b)
| anonymous,        anonymous        => isTrue rfl
| mkString p₁ s₁,  mkString p₂ s₂  =>
  if h₁ : s₁ = s₂ then
    match decEq p₁ p₂ with
    | isTrue h₂  => isTrue $ h₁ ▸ h₂ ▸ rfl
    | isFalse h₂ => isFalse $ fun h => Name.noConfusion h $ fun hp hs => absurd hp h₂
  else isFalse $ fun h => Name.noConfusion h $ fun hp hs => absurd hs h₁
| mkNumeral p₁ n₁, mkNumeral p₂ n₂ =>
  if h₁ : n₁ = n₂ then
    match decEq p₁ p₂ with
    | isTrue h₂  => isTrue $ h₁ ▸ h₂ ▸ rfl
    | isFalse h₂ => isFalse $ fun h => Name.noConfusion h $ fun hp hs => absurd hp h₂
  else isFalse $ fun h => Name.noConfusion h $ fun hp hs => absurd hs h₁
| anonymous,       mkString _ _    => isFalse $ fun h => Name.noConfusion h
| anonymous,       mkNumeral _ _   => isFalse $ fun h => Name.noConfusion h
| mkString _ _,    anonymous       => isFalse $ fun h => Name.noConfusion h
| mkString _ _,    mkNumeral _ _   => isFalse $ fun h => Name.noConfusion h
| mkNumeral _ _,   anonymous       => isFalse $ fun h => Name.noConfusion h
| mkNumeral _ _,   mkString _ _    => isFalse $ fun h => Name.noConfusion h

instance : DecidableEq Name :=
{decEq := Name.decEq}

def eqStr : Name → String → Bool
| mkString Name.anonymous s,   s' => s == s'
| _, _ => false

protected def append : Name → Name → Name
| n, anonymous => n
| n, mkString p s   =>
  mkString (append n p) s
| n, mkNumeral p d   =>
  mkNumeral (append n p) d

instance : HasAppend Name :=
⟨Name.append⟩

def replacePrefix : Name → Name → Name → Name
| anonymous, anonymous, newP => newP
| anonymous, _,         _     => anonymous
| n@(mkString p s), queryP, newP =>
  if n = queryP then
    newP
  else
    mkString (p.replacePrefix queryP newP) s
| n@(mkNumeral p s), queryP, newP =>
  if n = queryP then
    newP
  else
    mkNumeral (p.replacePrefix queryP newP) s

def isPrefixOf : Name → Name → Bool
| p, anonymous          => p == anonymous
| p, n@(mkNumeral p' _) => p == n || isPrefixOf p p'
| p, n@(mkString p' _)  => p == n || isPrefixOf p p'

def lt : Name → Name → Bool
| anonymous,       anonymous       => false
| anonymous,       _               => true
| mkNumeral p₁ i₁, mkNumeral p₂ i₂ => lt p₁ p₂ || (p₁ == p₂ && i₁ < i₂)
| mkNumeral _ _,   mkString _ _    => true
| mkString p₁ n₁,  mkString p₂ n₂  => lt p₁ p₂ || (p₁ == p₂ && n₁ < n₂)
| _,               _               => false

def quickLtAux : Name → Name → Bool
| anonymous,     anonymous       => false
| anonymous,     _               => true
| mkNumeral n v, mkNumeral n' v' => v < v' || (v = v' && n.quickLtAux n')
| mkNumeral _ _, mkString _ _    => true
| mkString n s,  mkString n' s'  => s < s' || (s = s' && n.quickLtAux n')
| _,              _              => false

def quickLt (n₁ n₂ : Name) : Bool :=
if n₁.hash < n₂.hash then true
else if n₁.hash > n₂.hash then false
else quickLtAux n₁ n₂

/- Alternative HasLt instance. -/
@[inline] protected def hasLtQuick : HasLess Name :=
⟨fun a b => Name.quickLt a b = true⟩

@[inline] instance : DecidableRel (@HasLess.Less Name Name.hasLtQuick) :=
inferInstanceAs (DecidableRel (fun a b => Name.quickLt a b = true))

def toStringWithSep (sep : String) : Name → String
| anonymous             => "[anonymous]"
| mkString anonymous s  => s
| mkNumeral anonymous v => toString v
| mkString n s          => toStringWithSep n ++ sep ++ s
| mkNumeral n v         => toStringWithSep n ++ sep ++ repr v

protected def toString : Name → String :=
toStringWithSep "."

instance : HasToString Name :=
⟨Name.toString⟩

def appendAfter : Name → String → Name
| mkString p s, suffix => mkString p (s ++ suffix)
| n,            suffix => mkString n suffix

def appendIndexAfter : Name → Nat → Name
| mkString p s, idx => mkString p (s ++ "_" ++ toString idx)
| n,            idx => mkString n ("_" ++ toString idx)

/- The frontend does not allow user declarations to start with `_` in any of its parts.
   We use name parts starting with `_` internally to create auxiliary names (e.g., `_private`). -/
def isInternal : Name → Bool
| mkString p s    => s.get 0 == '_' || isInternal p
| mkNumeral p _   => isInternal p
| _ => false

def isAtomic : Name → Bool
| anonymous => true
| mkString anonymous _ => true
| mkNumeral anonymous _ => true
| _ => false

theorem mkStringNeMkStringOfNePrefix {p₁ : Name} (s₁ : String) {p₂ : Name} (s₂ : String) : p₁ ≠ p₂ → mkString p₁ s₁ ≠ mkString p₂ s₂ :=
fun h₁ h₂ => Name.noConfusion h₂ (fun h _ => absurd h h₁)

theorem mkStringNeMkStringOfNeString (p₁ : Name) {s₁ : String} (p₂ : Name) {s₂ : String} : s₁ ≠ s₂ → mkString p₁ s₁ ≠ mkString p₂ s₂ :=
fun h₁ h₂ => Name.noConfusion h₂ (fun _ h => absurd h h₁)

theorem mkNumeralNeMkNumeralOfNePrefix {p₁ : Name} (n₁ : Nat) {p₂ : Name} (n₂ : Nat) : p₁ ≠ p₂ → mkNumeral p₁ n₁ ≠ mkNumeral p₂ n₂ :=
fun h₁ h₂ => Name.noConfusion h₂ (fun h _ => absurd h h₁)

theorem mkNumeralNeMkNumeralOfNeNumeral (p₁ : Name) {n₁ : Nat} (p₂ : Name) {n₂ : Nat} : n₁ ≠ n₂ → mkNumeral p₁ n₁ ≠ mkNumeral p₂ n₂ :=
fun h₁ h₂ => Name.noConfusion h₂ (fun _ h => absurd h h₁)

end Name

def NameMap (α : Type) := RBMap Name α Name.quickLt

@[inline] def mkNameMap (α : Type) : NameMap α := mkRBMap Name α Name.quickLt

namespace NameMap
variable {α : Type}

instance (α : Type) : HasEmptyc (NameMap α) := ⟨mkNameMap α⟩

instance (α : Type) : Inhabited (NameMap α) := ⟨{}⟩

def insert (m : NameMap α) (n : Name) (a : α) := RBMap.insert m n a

def contains (m : NameMap α) (n : Name) : Bool := RBMap.contains m n

@[inline] def find (m : NameMap α) (n : Name) : Option α := RBMap.find m n

end NameMap

def NameSet := RBTree Name Name.quickLt

@[inline] def mkNameSet : NameSet := mkRBTree Name Name.quickLt

namespace NameSet

instance : HasEmptyc NameSet := ⟨mkNameSet⟩

instance : Inhabited NameSet := ⟨{}⟩

def insert (s : NameSet) (n : Name)  := RBTree.insert s n

def contains (s : NameSet) (n : Name) : Bool := RBMap.contains s n

end NameSet

def mkNameStr (p : Name) (s : String) : Name :=
Name.mkString p s

def mkNameNum (p : Name) (v : Nat) : Name :=
Name.mkNumeral p v

end Lean

open Lean

def String.toName (s : String) : Name :=
let ps := s.splitOn ".";
ps.foldl (fun n p => Name.mkString n p.trim) Name.anonymous
