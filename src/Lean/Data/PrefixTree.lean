/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.RBMap

namespace Lean

/- Similar to trie, but for arbitrary keys -/
inductive PrefixTreeNode (α : Type u) (β : Type v) where
  | Node : Option β → RBNode α (fun _ => PrefixTreeNode α β) → PrefixTreeNode α β

instance : Inhabited (PrefixTreeNode α β) where
  default := PrefixTreeNode.Node none RBNode.leaf

namespace PrefixTreeNode

def empty : PrefixTreeNode α β :=
  PrefixTreeNode.Node none RBNode.leaf

@[specialize]
partial def insert (t : PrefixTreeNode α β) (cmp : α → α → Ordering) (k : List α) (val : β) : PrefixTreeNode α β :=
  let rec insertEmpty (k : List α) : PrefixTreeNode α β :=
    match k with
    | [] => PrefixTreeNode.Node (some val) RBNode.leaf
    | k :: ks =>
      let t := insertEmpty ks
      PrefixTreeNode.Node none (RBNode.singleton k t)
  let rec loop
    | PrefixTreeNode.Node _ m, [] =>
      PrefixTreeNode.Node (some val) m -- overrides old value
    | PrefixTreeNode.Node v m, k :: ks =>
      let t := match RBNode.find cmp m k with
        | none   => insertEmpty ks
        | some t => loop t ks
      PrefixTreeNode.Node v (RBNode.insert cmp m k t)
  loop t k

@[specialize]
partial def find? (t : PrefixTreeNode α β) (cmp : α → α → Ordering) (k : List α) : Option β :=
  let rec loop
    | PrefixTreeNode.Node val _, [] => val
    | PrefixTreeNode.Node _   m, k :: ks =>
      match RBNode.find cmp m k with
      | none   => none
      | some t => loop t ks
  loop t k

/-- Returns the the value of the longest key in `t` that is a prefix of `k`, if any. -/
@[specialize]
partial def findLongestPrefix? (t : PrefixTreeNode α β) (cmp : α → α → Ordering) (k : List α) : Option β :=
  let rec loop acc?
    | PrefixTreeNode.Node val _, [] => val <|> acc?
    | PrefixTreeNode.Node val m, k :: ks =>
      match RBNode.find cmp m k with
      | none   => val
      | some t => loop (val <|> acc?) t ks
  loop none t k

@[specialize]
partial def foldMatchingM [Monad m] (t : PrefixTreeNode α β) (cmp : α → α → Ordering) (k : List α) (init : σ) (f : β → σ → m σ) : m σ :=
  let rec fold : PrefixTreeNode α β → σ → m σ
    | PrefixTreeNode.Node b? n, d => do
      let d ← match b? with
        | none   => pure d
        | some b => f b d
      n.foldM (init := d) fun d _ t => fold t d
  let rec find : List α → PrefixTreeNode α β → σ → m σ
    | [],    t, d => fold t d
    | k::ks, PrefixTreeNode.Node _ m, d =>
      match RBNode.find cmp m k with
      | none   => pure init
      | some t => find ks t d
  find k t init

inductive WellFormed (cmp : α → α → Ordering) : PrefixTreeNode α β → Prop where
  | emptyWff  : WellFormed cmp empty
  | insertWff : WellFormed cmp t → WellFormed cmp (insert t cmp k val)

end PrefixTreeNode

def PrefixTree (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Type (max u v) :=
  { t : PrefixTreeNode α β // t.WellFormed cmp }

open PrefixTreeNode

def PrefixTree.empty : PrefixTree α β p :=
  ⟨PrefixTreeNode.empty, WellFormed.emptyWff⟩

instance : Inhabited (PrefixTree α β p) where
  default := PrefixTree.empty

instance : EmptyCollection (PrefixTree α β p) where
  emptyCollection := PrefixTree.empty

@[inline]
def PrefixTree.insert (t : PrefixTree α β p) (k : List α) (v : β) : PrefixTree α β p :=
  ⟨t.val.insert p k v, WellFormed.insertWff t.property⟩

@[inline]
def PrefixTree.find? (t : PrefixTree α β p) (k : List α) : Option β :=
  t.val.find? p k

@[inline]
def PrefixTree.findLongestPrefix? (t : PrefixTree α β p) (k : List α) : Option β :=
  t.val.findLongestPrefix? p k

@[inline]
def PrefixTree.foldMatchingM [Monad m] (t : PrefixTree α β p) (k : List α) (init : σ) (f : β → σ → m σ) : m σ :=
  t.val.foldMatchingM p k init f

@[inline]
def PrefixTree.foldM [Monad m] (t : PrefixTree α β p) (init : σ) (f : β → σ → m σ) : m σ :=
  t.foldMatchingM [] init f

@[inline]
def PrefixTree.forMatchingM [Monad m] (t : PrefixTree α β p) (k : List α) (f : β → m Unit) : m Unit :=
  t.val.foldMatchingM p k () (fun b _ => f b)

@[inline]
def PrefixTree.forM [Monad m] (t : PrefixTree α β p) (f : β → m Unit) : m Unit :=
  t.forMatchingM [] f

end Lean
