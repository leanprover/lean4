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
| str : Name → String → Name
| num : Name → Nat → Name

attribute [extern "lean_name_mk_string"] Name.str
attribute [extern "lean_name_mk_numeral"] Name.num

instance : Inhabited Name :=
⟨Name.anonymous⟩

def mkNameStr (p : Name) (s : String) : Name :=
Name.str p s

def mkNameNum (p : Name) (v : Nat) : Name :=
Name.num p v

def mkNameSimple (s : String) : Name :=
mkNameStr Name.anonymous s

instance stringToName : HasCoe String Name :=
⟨mkNameSimple⟩

namespace Name
@[extern "lean_name_hash_usize"]
constant hash (n : @& Name) : USize := arbitrary _

instance : Hashable Name :=
⟨Name.hash⟩

def getPrefix : Name → Name
| anonymous => anonymous
| str p s   => p
| num p s   => p

def getNumParts : Name → Nat
| anonymous => 0
| str p _   => getNumParts p + 1
| num p _   => getNumParts p + 1

def updatePrefix : Name → Name → Name
| anonymous, newP => anonymous
| str p s,   newP => mkNameStr newP s
| num p s,   newP => mkNameNum newP s

def components' : Name → List Name
| anonymous => []
| str n s   => mkNameStr anonymous s :: components' n
| num n v   => mkNameNum anonymous v :: components' n

def components (n : Name) : List Name :=
n.components'.reverse

protected def beq : Name → Name → Bool
| anonymous, anonymous => true
| str p₁ s₁, str p₂ s₂ => s₁ == s₂ && beq p₁ p₂
| num p₁ n₁, num p₂ n₂ => n₁ == n₂ && beq p₁ p₂
| _,         _         => false

instance : HasBeq Name := ⟨Name.beq⟩

def eqStr : Name → String → Bool
| str anonymous s, s' => s == s'
| _,               _  => false

protected def append : Name → Name → Name
| n, anonymous => n
| n, str p s   => mkNameStr (append n p) s
| n, num p d   => mkNameNum (append n p) d

instance : HasAppend Name :=
⟨Name.append⟩

def replacePrefix : Name → Name → Name → Name
| anonymous,   anonymous, newP => newP
| anonymous,   _,         _    => anonymous
| n@(str p s), queryP,    newP => if n == queryP then newP else mkNameStr (p.replacePrefix queryP newP) s
| n@(num p s), queryP,    newP => if n == queryP then newP else mkNameNum (p.replacePrefix queryP newP) s

def isPrefixOf : Name → Name → Bool
| p, anonymous    => p == anonymous
| p, n@(num p' _) => p == n || isPrefixOf p p'
| p, n@(str p' _) => p == n || isPrefixOf p p'

def lt : Name → Name → Bool
| anonymous, anonymous => false
| anonymous, _         => true
| num p₁ i₁, num p₂ i₂ => lt p₁ p₂ || (p₁ == p₂ && i₁ < i₂)
| num _ _,   str _ _   => true
| str p₁ n₁, str p₂ n₂ => lt p₁ p₂ || (p₁ == p₂ && n₁ < n₂)
| _,               _   => false

def quickLtAux : Name → Name → Bool
| anonymous, anonymous => false
| anonymous, _         => true
| num n v,   num n' v' => v < v' || (v = v' && n.quickLtAux n')
| num _ _,   str _ _   => true
| str n s,   str n' s' => s < s' || (s = s' && n.quickLtAux n')
| _,              _    => false

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
| anonymous       => "[anonymous]"
| str anonymous s => s
| num anonymous v => toString v
| str n s         => toStringWithSep n ++ sep ++ s
| num n v         => toStringWithSep n ++ sep ++ repr v

protected def toString : Name → String :=
toStringWithSep "."

instance : HasToString Name :=
⟨Name.toString⟩

def appendAfter : Name → String → Name
| str p s, suffix => mkNameStr p (s ++ suffix)
| n,       suffix => mkNameStr n suffix

def appendIndexAfter : Name → Nat → Name
| str p s, idx => mkNameStr p (s ++ "_" ++ toString idx)
| n,       idx => mkNameStr n ("_" ++ toString idx)

/- The frontend does not allow user declarations to start with `_` in any of its parts.
   We use name parts starting with `_` internally to create auxiliary names (e.g., `_private`). -/
def isInternal : Name → Bool
| str p s => s.get 0 == '_' || isInternal p
| num p _ => isInternal p
| _        => false

def isAtomic : Name → Bool
| anonymous       => true
| str anonymous _ => true
| num anonymous _ => true
| _               => false

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
end Lean

open Lean

def String.toName (s : String) : Name :=
let ps := s.splitOn ".";
ps.foldl (fun n p => mkNameStr n p.trim) Name.anonymous
