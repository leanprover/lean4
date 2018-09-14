/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Trie for tokenizing the Lean language
-/
namespace lean.parser

inductive trie (α : Type)
| node : option α → rbnode (char × trie) → trie

namespace trie
variables {α : Type}

protected def mk : trie α :=
⟨none, rbnode.leaf⟩

private def insert_aux (val : α) : nat → trie α → string.iterator → trie α
| 0     (trie.node _ map)    _ := trie.node (some val) map   -- NOTE: overrides old value
| (n+1) (trie.node val map) it :=
  let t' := (rbmap_core.find (<) map it.curr).get_or_else trie.mk in
  trie.node val (rbmap_core.insert (<) map it.curr (insert_aux n t' it.next))

def insert (t : trie α) (s : string) (val : α) : trie α :=
insert_aux val s.length t s.mk_iterator

private def match_prefix_aux : nat → trie α → string.iterator → option (string.iterator × α) → option (string.iterator × α)
| 0     (trie.node val map) it acc := prod.mk it <$> val <|> acc
| (n+1) (trie.node val map) it acc :=
  let acc' := prod.mk it <$> val <|> acc in
  match rbmap_core.find (<) map it.curr with
    | some t := match_prefix_aux n t it.next acc'
    | none   := acc'

def match_prefix {α : Type} (t : trie α) (it : string.iterator) : option (string.iterator × α) :=
match_prefix_aux it.remaining t it none
end trie

end lean.parser
