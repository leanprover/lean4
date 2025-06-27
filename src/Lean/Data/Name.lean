/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Ord
namespace Lean

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

def componentsRev : Name → List Name
  | anonymous => []
  | str n s   => Name.mkStr anonymous s :: componentsRev n
  | num n v   => Name.mkNum anonymous v :: componentsRev n

def components (n : Name) : List Name :=
  n.componentsRev.reverse

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

/-- Returns true if the name has any numeric components. -/
def hasNum : Name → Bool
  | .anonymous => false
  | .str p _ => p.hasNum
  | .num _ _ => true

/-- The frontend does not allow user declarations to start with `_` in any of its parts.
   We use name parts starting with `_` internally to create auxiliary names (e.g., `_private`). -/
def isInternal : Name → Bool
  | str p s => s.get 0 == '_' || isInternal p
  | num p _ => isInternal p
  | _       => false

/--
The frontend does not allow user declarations to start with `_` in any of its parts.
We use name parts starting with `_` internally to create auxiliary names (e.g., `_private`).

This function checks if any component of the name starts with `_`, or is numeric.
-/
def isInternalOrNum : Name → Bool
  | .str p s => s.get 0 == '_' || isInternalOrNum p
  | .num _ _ => true
  | _       => false

/--
Returns true if this a part of name that is internal or dynamically
generated so that it may easily be changed.

Generally, user code should not explicitly use internal names.
-/
def isInternalDetail : Name → Bool
  | .str p s     =>
    s.startsWith "_"
      || matchPrefix s "eq_"
      || matchPrefix s "match_"
      || matchPrefix s "proof_"
      || matchPrefix s "omega_"
      || p.isInternalOrNum
  | .num _ _     => true
  | p            => p.isInternalOrNum
where
  /-- Check that a string begins with the given prefix, and then is only digits/'_'. -/
  matchPrefix (s : String) (pre : String) :=
    s.startsWith pre && (s |>.drop pre.length |>.all fun c => c.isDigit || c == '_')

/--
Checks whether the name is an implementation-detail hypothesis name.

Implementation-detail hypothesis names start with a double underscore.
-/
def isImplementationDetail : Name → Bool
  | str anonymous s => s.startsWith "__"
  | num p _ => p.isImplementationDetail
  | str p _ => p.isImplementationDetail
  | anonymous => false

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

/--
Return `true` if `n` contains a string part `s` that satisfies `f`.

Examples:
```
#eval (`foo.bla).anyS (·.startsWith "fo") -- true
#eval (`foo.bla).anyS (·.startsWith "boo") -- false
```
-/
def anyS (n : Name) (f : String → Bool) : Bool :=
  match n with
  | .str p s => f s || p.anyS f
  | .num p _ => p.anyS f
  | _ => false

/-- Return true if the name is in a namespace associated to metaprogramming. -/
def isMetaprogramming (n : Name) : Bool :=
  let components := n.components
  components.head? == some `Lean || (components.any fun n => n == `Tactic || n == `Linter)

end Name
end Lean

open Lean
