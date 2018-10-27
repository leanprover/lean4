/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Trie for tokenizing the Lean language
-/
prelude
import init.data.rbmap
import init.lean.format

namespace lean
namespace parser

inductive trie (α : Type)
| node : option α → rbnode char (λ _, trie) → trie

namespace trie
variables {α : Type}

protected def mk : trie α :=
⟨none, rbnode.leaf⟩

private def insert_aux (val : α) : nat → trie α → string.iterator → trie α
| 0     (trie.node _ map)    _ := trie.node (some val) map   -- NOTE: overrides old value
| (n+1) (trie.node val map) it :=
  let t' := (rbnode.find (<) map it.curr).get_or_else trie.mk in
  trie.node val (rbnode.insert (<) map it.curr (insert_aux n t' it.next))

def insert (t : trie α) (s : string) (val : α) : trie α :=
insert_aux val s.length t s.mk_iterator

private def find_aux : nat → trie α → string.iterator → option α
| 0     (trie.node val _)    _ := val
| (n+1) (trie.node val map) it := do
  t' ← rbnode.find (<) map it.curr,
  find_aux n t' it.next

def find (t : trie α) (s : string) : option α :=
find_aux s.length t s.mk_iterator

private def match_prefix_aux : nat → trie α → string.iterator → option (string.iterator × α) → option (string.iterator × α)
| 0     (trie.node val map) it acc := prod.mk it <$> val <|> acc
| (n+1) (trie.node val map) it acc :=
  let acc' := prod.mk it <$> val <|> acc in
  match rbnode.find (<) map it.curr with
    | some t := match_prefix_aux n t it.next acc'
    | none   := acc'

def match_prefix {α : Type} (t : trie α) (it : string.iterator) : option (string.iterator × α) :=
match_prefix_aux it.remaining t it none

private def to_string_aux {α : Type} : trie α → list format
| (trie.node val map) := flip rbnode.fold map (λ c t fs,
  to_format (repr c) :: (format.group $ format.nest 2 $ flip format.join_sep format.line $ to_string_aux t) :: fs) []

instance {α : Type} : has_to_string (trie α) :=
⟨λ t, (flip format.join_sep format.line $ to_string_aux t).pretty 0⟩
end trie

end parser
end lean
