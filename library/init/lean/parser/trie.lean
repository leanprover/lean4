/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Trie for tokenizing the Lean language
-/
prelude
import init.data.rbmap
import init.lean.format

namespace Lean
namespace Parser

inductive Trie (α : Type)
| Node : Option α → RBNode Char (λ _, Trie) → Trie

namespace Trie
variables {α : Type}

protected def mk : Trie α :=
⟨none, RBNode.leaf⟩

private def insertAux (val : α) : Nat → Trie α → String.Iterator → Trie α
| 0     (Trie.Node _ map)    _ := Trie.Node (some val) map   -- NOTE: overrides old value
| (n+1) (Trie.Node val map) it :=
  let t' := (RBNode.find (<) map it.curr).getOrElse Trie.mk in
  Trie.Node val (RBNode.insert (<) map it.curr (insertAux n t' it.next))

def insert (t : Trie α) (s : String) (val : α) : Trie α :=
insertAux val s.length t s.mkIterator

private def findAux : Nat → Trie α → String.Iterator → Option α
| 0     (Trie.Node val _)    _ := val
| (n+1) (Trie.Node val map) it := do
  t' ← RBNode.find (<) map it.curr,
  findAux n t' it.next

def find (t : Trie α) (s : String) : Option α :=
findAux s.length t s.mkIterator

private def matchPrefixAux : Nat → Trie α → String.Iterator → Option (String.Iterator × α) → Option (String.Iterator × α)
| 0     (Trie.Node val map) it Acc := Prod.mk it <$> val <|> Acc
| (n+1) (Trie.Node val map) it Acc :=
  let Acc' := Prod.mk it <$> val <|> Acc in
  match RBNode.find (<) map it.curr with
    | some t := matchPrefixAux n t it.next Acc'
    | none   := Acc'

def matchPrefix {α : Type} (t : Trie α) (it : String.Iterator) : Option (String.Iterator × α) :=
matchPrefixAux it.remaining t it none

private def toStringAux {α : Type} : Trie α → List Format
| (Trie.Node val map) := flip RBNode.fold map (λ c t Fs,
  toFormat (repr c) :: (Format.group $ Format.nest 2 $ flip Format.joinSep Format.line $ toStringAux t) :: Fs) []

instance {α : Type} : HasToString (Trie α) :=
⟨λ t, (flip Format.joinSep Format.line $ toStringAux t).pretty 0⟩
end Trie

end Parser
end Lean
