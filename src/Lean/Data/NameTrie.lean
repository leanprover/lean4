/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.PrefixTree

namespace Lean

inductive NamePart
  | str (s : String)
  | num (n : Nat)

instance : ToString NamePart where
  toString
    | NamePart.str s => s
    | NamePart.num n => toString n

def NamePart.cmp : NamePart → NamePart → Ordering
  | NamePart.str a, NamePart.str b => compare a b
  | NamePart.num a, NamePart.num b => compare a b
  | NamePart.num _, NamePart.str _ => Ordering.lt
  | _, _ => Ordering.gt

def NamePart.lt : NamePart → NamePart → Bool
  | NamePart.str a, NamePart.str b => a < b
  | NamePart.num a, NamePart.num b => a < b
  | NamePart.num _, NamePart.str _ => true
  | _, _ => false

def NameTrie (β : Type u) := PrefixTree NamePart β NamePart.cmp

private def toKey (n : Name) : List NamePart :=
  loop n []
where
  loop
    | Name.str p s,   parts => loop p (NamePart.str s :: parts)
    | Name.num p n,   parts => loop p (NamePart.num n :: parts)
    | Name.anonymous, parts => parts

def NameTrie.insert (t : NameTrie β) (n : Name) (b : β) : NameTrie β :=
  PrefixTree.insert t (toKey n) b

def NameTrie.empty : NameTrie β :=
  PrefixTree.empty

instance : Inhabited (NameTrie β) where
  default := NameTrie.empty

instance : EmptyCollection (NameTrie β) where
  emptyCollection := NameTrie.empty

def NameTrie.find? (t : NameTrie β) (k : Name) : Option β :=
  PrefixTree.find? t (toKey k)

@[inline]
def NameTrie.foldMatchingM [Monad m] (t : NameTrie β) (k : Name) (init : σ) (f : β → σ → m σ) : m σ :=
  PrefixTree.foldMatchingM t (toKey k) init f

@[inline]
def NameTrie.foldM [Monad m] (t : NameTrie β) (init : σ) (f : β → σ → m σ) : m σ :=
  t.foldMatchingM Name.anonymous init f

@[inline]
def NameTrie.forMatchingM [Monad m] (t : NameTrie β) (k : Name) (f : β → m Unit) : m Unit :=
  PrefixTree.forMatchingM t (toKey k) f

@[inline]
def NameTrie.forM [Monad m] (t : NameTrie β) (f : β → m Unit) : m Unit :=
  t.forMatchingM Name.anonymous f

def NameTrie.matchingToArray (t : NameTrie β) (k : Name) : Array β :=
  Id.run <| t.foldMatchingM k #[] fun v acc => acc.push v

def NameTrie.toArray (t : NameTrie β) : Array β :=
  Id.run <| t.foldM #[] fun v acc => acc.push v

end Lean
