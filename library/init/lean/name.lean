/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.coe init.data.uint init.data.toString
import init.lean.format init.data.hashable init.data.rbmap init.data.rbtree
namespace lean

inductive name
| anonymous  : name
| mkString  : name → string → name
| mkNumeral : name → nat → name

attribute [extern "lean_name_mk_string"] name.mkString
attribute [extern "lean_name_mk_numeral"] name.mkNumeral

instance : inhabited name :=
⟨name.anonymous⟩

def mkStrName (p : name) (s : string) : name :=
name.mkString p s

def mkNumName (p : name) (v : nat) : name :=
name.mkNumeral p v

def mkSimpleName (s : string) : name :=
mkStrName name.anonymous s

instance stringToName : hasCoe string name :=
⟨mkSimpleName⟩

namespace name
@[extern "lean_name_hash_usize"]
constant hash (n : @& name) : usize := default usize

instance : hashable name :=
⟨name.hash⟩

def getPrefix : name → name
| anonymous        := anonymous
| (mkString p s)  := p
| (mkNumeral p s) := p

def updatePrefix : name → name → name
| anonymous        newP := anonymous
| (mkString p s)  newP := mkString newP s
| (mkNumeral p s) newP := mkNumeral newP s

def components' : name → list name
| anonymous                := []
| (mkString n s)          := mkString anonymous s :: components' n
| (mkNumeral n v)         := mkNumeral anonymous v :: components' n

def components (n : name) : list name :=
n.components'.reverse

@[extern "lean_name_dec_eq"]
protected def decEq : Π (a b : @& name), decidable (a = b)
| anonymous          anonymous          := isTrue rfl
| (mkString p₁ s₁)  (mkString p₂ s₂)  :=
  if h₁ : s₁ = s₂ then
    match decEq p₁ p₂ with
    | isTrue h₂  := isTrue $ h₁ ▸ h₂ ▸ rfl
    | isFalse h₂ := isFalse $ λ h, name.noConfusion h $ λ hp hs, absurd hp h₂
  else isFalse $ λ h, name.noConfusion h $ λ hp hs, absurd hs h₁
| (mkNumeral p₁ n₁) (mkNumeral p₂ n₂) :=
  if h₁ : n₁ = n₂ then
    match decEq p₁ p₂ with
    | isTrue h₂  := isTrue $ h₁ ▸ h₂ ▸ rfl
    | isFalse h₂ := isFalse $ λ h, name.noConfusion h $ λ hp hs, absurd hp h₂
  else isFalse $ λ h, name.noConfusion h $ λ hp hs, absurd hs h₁
| anonymous          (mkString _ _)    := isFalse $ λ h, name.noConfusion h
| anonymous          (mkNumeral _ _)   := isFalse $ λ h, name.noConfusion h
| (mkString _ _)    anonymous          := isFalse $ λ h, name.noConfusion h
| (mkString _ _)    (mkNumeral _ _)   := isFalse $ λ h, name.noConfusion h
| (mkNumeral _ _)   anonymous          := isFalse $ λ h, name.noConfusion h
| (mkNumeral _ _)   (mkString _ _)    := isFalse $ λ h, name.noConfusion h

instance : decidableEq name :=
{decEq := name.decEq}

protected def append : name → name → name
| n anonymous := n
| n (mkString p s) :=
  mkString (append n p) s
| n (mkNumeral p d) :=
  mkNumeral (append n p) d

instance : hasAppend name :=
⟨name.append⟩

def replacePrefix : name → name → name → name
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

def quickLtCore : name → name → bool
| anonymous        anonymous          := ff
| anonymous        _                  := tt
| (mkNumeral n v) (mkNumeral n' v') := v < v' || (v = v' && n.quickLtCore n')
| (mkNumeral _ _) (mkString _ _)    := tt
| (mkString n s)  (mkString n' s')  := s < s' || (s = s' && n.quickLtCore n')
| _                _                  := ff

def quickLt (n₁ n₂ : name) : bool :=
if n₁.hash < n₂.hash then tt
else if n₁.hash > n₂.hash then ff
else quickLtCore n₁ n₂

/- Alternative hasLt instance. -/
@[inline] protected def hasLtQuick : hasLt name :=
⟨λ a b, name.quickLt a b = tt⟩

@[inline] instance : decidableRel (@hasLt.lt name name.hasLtQuick) :=
inferInstanceAs (decidableRel (λ a b, name.quickLt a b = tt))

def toStringWithSep (sep : string) : name → string
| anonymous                := "[anonymous]"
| (mkString anonymous s)  := s
| (mkNumeral anonymous v) := toString v
| (mkString n s)          := toStringWithSep n ++ sep ++ s
| (mkNumeral n v)         := toStringWithSep n ++ sep ++ repr v

protected def toString : name → string :=
toStringWithSep "."

instance : hasToString name :=
⟨name.toString⟩

instance : hasToFormat name :=
⟨λ n, n.toString⟩

theorem mkStringNeMkStringOfNePrefix {p₁ : name} (s₁ : string) {p₂ : name} (s₂ : string) : p₁ ≠ p₂ → mkString p₁ s₁ ≠ mkString p₂ s₂ :=
λ h₁ h₂, name.noConfusion h₂ (λ h _, absurd h h₁)

theorem mkStringNeMkStringOfNeString (p₁ : name) {s₁ : string} (p₂ : name) {s₂ : string} : s₁ ≠ s₂ → mkString p₁ s₁ ≠ mkString p₂ s₂ :=
λ h₁ h₂, name.noConfusion h₂ (λ _ h, absurd h h₁)

theorem mkNumeralNeMkNumeralOfNePrefix {p₁ : name} (n₁ : nat) {p₂ : name} (n₂ : nat) : p₁ ≠ p₂ → mkNumeral p₁ n₁ ≠ mkNumeral p₂ n₂ :=
λ h₁ h₂, name.noConfusion h₂ (λ h _, absurd h h₁)

theorem mkNumeralNeMkNumeralOfNeNumeral (p₁ : name) {n₁ : nat} (p₂ : name) {n₂ : nat} : n₁ ≠ n₂ → mkNumeral p₁ n₁ ≠ mkNumeral p₂ n₂ :=
λ h₁ h₂, name.noConfusion h₂ (λ _ h, absurd h h₁)

end name

section
local attribute [instance] name.hasLtQuick
def nameMap (α : Type) := rbmap name α (<)
variable {α : Type}
@[inline] def mkNameMap : nameMap α :=
mkRbmap name α (<)
def nameMap.insert (m : nameMap α) (n : name) (a : α) :=
rbmap.insert m n a
def nameMap.contains (m : nameMap α) (n : name) : bool :=
rbmap.contains m n
@[inline] def nameMap.find (m : nameMap α) (n : name) : option α :=
rbmap.find m n
end

section
local attribute [instance] name.hasLtQuick
def nameSet := rbtree name (<)
@[inline] def mkNameSet : nameSet :=
mkRbtree name (<)
def nameSet.insert (s : nameSet) (n : name)  :=
rbtree.insert s n
def nameSet.contains (s : nameSet) (n : name) : bool :=
rbmap.contains s n
end

end lean
