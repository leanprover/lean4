/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.coe init.data.uint init.data.tostring
import init.lean.format init.data.hashable init.data.rbmap init.data.rbtree
namespace Lean

inductive Name
| anonymous  : Name
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
constant hash (n : @& Name) : Usize := default Usize

instance : Hashable Name :=
⟨Name.hash⟩

def getPrefix : Name → Name
| anonymous       := anonymous
| (mkString p s)  := p
| (mkNumeral p s) := p

def updatePrefix : Name → Name → Name
| anonymous       newP := anonymous
| (mkString p s)  newP := mkString newP s
| (mkNumeral p s) newP := mkNumeral newP s

def components' : Name → List Name
| anonymous               := []
| (mkString n s)          := mkString anonymous s :: components' n
| (mkNumeral n v)         := mkNumeral anonymous v :: components' n

def components (n : Name) : List Name :=
n.components'.reverse

@[extern "lean_name_dec_eq"]
protected def decEq : Π (a b : @& Name), Decidable (a = b)
| anonymous          anonymous          := isTrue rfl
| (mkString p₁ s₁)  (mkString p₂ s₂)  :=
  if h₁ : s₁ = s₂ then
    match decEq p₁ p₂ with
    | isTrue h₂  := isTrue $ h₁ ▸ h₂ ▸ rfl
    | isFalse h₂ := isFalse $ λ h, Name.noConfusion h $ λ hp hs, absurd hp h₂
  else isFalse $ λ h, Name.noConfusion h $ λ hp hs, absurd hs h₁
| (mkNumeral p₁ n₁) (mkNumeral p₂ n₂) :=
  if h₁ : n₁ = n₂ then
    match decEq p₁ p₂ with
    | isTrue h₂  := isTrue $ h₁ ▸ h₂ ▸ rfl
    | isFalse h₂ := isFalse $ λ h, Name.noConfusion h $ λ hp hs, absurd hp h₂
  else isFalse $ λ h, Name.noConfusion h $ λ hp hs, absurd hs h₁
| anonymous         (mkString _ _)    := isFalse $ λ h, Name.noConfusion h
| anonymous         (mkNumeral _ _)   := isFalse $ λ h, Name.noConfusion h
| (mkString _ _)    anonymous         := isFalse $ λ h, Name.noConfusion h
| (mkString _ _)    (mkNumeral _ _)   := isFalse $ λ h, Name.noConfusion h
| (mkNumeral _ _)   anonymous         := isFalse $ λ h, Name.noConfusion h
| (mkNumeral _ _)   (mkString _ _)    := isFalse $ λ h, Name.noConfusion h

instance : DecidableEq Name :=
{decEq := Name.decEq}

protected def append : Name → Name → Name
| n anonymous := n
| n (mkString p s) :=
  mkString (append n p) s
| n (mkNumeral p d) :=
  mkNumeral (append n p) d

instance : HasAppend Name :=
⟨Name.append⟩

def replacePrefix : Name → Name → Name → Name
| anonymous anonymous newP := newP
| anonymous _         _     := anonymous
| n@(mkString p s) queryP newP :=
  if n = queryP then
    newP
  else
    mkString (p.replacePrefix queryP newP) s
| n@(mkNumeral p s) queryP newP :=
  if n = queryP then
    newP
  else
    mkNumeral (p.replacePrefix queryP newP) s

def quickLtCore : Name → Name → Bool
| anonymous        anonymous          := false
| anonymous        _                  := true
| (mkNumeral n v) (mkNumeral n' v')   := v < v' || (v = v' && n.quickLtCore n')
| (mkNumeral _ _) (mkString _ _)      := true
| (mkString n s)  (mkString n' s')    := s < s' || (s = s' && n.quickLtCore n')
| _                _                  := false

def quickLt (n₁ n₂ : Name) : Bool :=
if n₁.hash < n₂.hash then true
else if n₁.hash > n₂.hash then false
else quickLtCore n₁ n₂

/- Alternative HasLt instance. -/
@[inline] protected def hasLtQuick : HasLt Name :=
⟨λ a b, Name.quickLt a b = true⟩

@[inline] instance : DecidableRel (@HasLt.lt Name Name.hasLtQuick) :=
inferInstanceAs (DecidableRel (λ a b, Name.quickLt a b = true))

def toStringWithSep (sep : String) : Name → String
| anonymous                := "[anonymous]"
| (mkString anonymous s)  := s
| (mkNumeral anonymous v) := toString v
| (mkString n s)          := toStringWithSep n ++ sep ++ s
| (mkNumeral n v)         := toStringWithSep n ++ sep ++ repr v

protected def toString : Name → String :=
toStringWithSep "."

instance : HasToString Name :=
⟨Name.toString⟩

instance : HasToFormat Name :=
⟨λ n, n.toString⟩

theorem mkStringNeMkStringOfNePrefix {p₁ : Name} (s₁ : String) {p₂ : Name} (s₂ : String) : p₁ ≠ p₂ → mkString p₁ s₁ ≠ mkString p₂ s₂ :=
λ h₁ h₂, Name.noConfusion h₂ (λ h _, absurd h h₁)

theorem mkStringNeMkStringOfNeString (p₁ : Name) {s₁ : String} (p₂ : Name) {s₂ : String} : s₁ ≠ s₂ → mkString p₁ s₁ ≠ mkString p₂ s₂ :=
λ h₁ h₂, Name.noConfusion h₂ (λ _ h, absurd h h₁)

theorem mkNumeralNeMkNumeralOfNePrefix {p₁ : Name} (n₁ : Nat) {p₂ : Name} (n₂ : Nat) : p₁ ≠ p₂ → mkNumeral p₁ n₁ ≠ mkNumeral p₂ n₂ :=
λ h₁ h₂, Name.noConfusion h₂ (λ h _, absurd h h₁)

theorem mkNumeralNeMkNumeralOfNeNumeral (p₁ : Name) {n₁ : Nat} (p₂ : Name) {n₂ : Nat} : n₁ ≠ n₂ → mkNumeral p₁ n₁ ≠ mkNumeral p₂ n₂ :=
λ h₁ h₂, Name.noConfusion h₂ (λ _ h, absurd h h₁)

end Name

section
local attribute [instance] Name.hasLtQuick
def NameMap (α : Type) := Rbmap Name α (<)
variable {α : Type}
@[inline] def mkNameMap : NameMap α :=
mkRbmap Name α (<)
def NameMap.insert (m : NameMap α) (n : Name) (a : α) :=
Rbmap.insert m n a
def NameMap.contains (m : NameMap α) (n : Name) : Bool :=
Rbmap.contains m n
@[inline] def NameMap.find (m : NameMap α) (n : Name) : Option α :=
Rbmap.find m n
end

section
local attribute [instance] Name.hasLtQuick
def NameSet := Rbtree Name (<)
@[inline] def mkNameSet : NameSet :=
mkRbtree Name (<)
def NameSet.insert (s : NameSet) (n : Name)  :=
Rbtree.insert s n
def NameSet.contains (s : NameSet) (n : Name) : Bool :=
Rbmap.contains s n
end

end Lean
