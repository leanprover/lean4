/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Std.Data.TreeMap.Raw.Basic

public section

namespace Lean

/-- Similar to trie, but for arbitrary keys -/
inductive PrefixTreeNode (α : Type u) (β : Type v) (cmp : α → α → Ordering) where
  | Node : Option β → Std.TreeMap.Raw α (PrefixTreeNode α β cmp) cmp → PrefixTreeNode α β cmp

instance : Inhabited (PrefixTreeNode α β cmp) where
  default := PrefixTreeNode.Node none ∅

namespace PrefixTreeNode

def empty : PrefixTreeNode α β cmp :=
  PrefixTreeNode.Node none ∅

@[inline]
partial def insert (cmp : α → α → Ordering) (t : PrefixTreeNode α β cmp) (k : Array α) (val : β) : PrefixTreeNode α β cmp :=
  let rec @[specialize] insertEmpty (idx : Nat) : PrefixTreeNode α β cmp :=
    if h : idx < k.size then
      let t := insertEmpty (idx + 1)
      PrefixTreeNode.Node none {(k[idx], t)}
    else
      PrefixTreeNode.Node (some val) ∅
  let rec @[specialize] loop (node : PrefixTreeNode α β cmp) (idx : Nat) :=
    match node with
    | .Node v m =>
      if h : idx < k.size then
          let elem := k[idx]
          let t := match m.get? elem with
            | none   => insertEmpty (idx + 1)
            | some t => loop t (idx + 1)
          PrefixTreeNode.Node v (m.insert elem t)
      else
        PrefixTreeNode.Node (some val) m -- overrides old value
  loop t 0

@[specialize]
partial def find? (cmp : α → α → Ordering) (t : PrefixTreeNode α β cmp) (k : Array α) : Option β :=
  let rec @[specialize] loop (node : PrefixTreeNode α β cmp) (idx : Nat) :=
    match node with
    | .Node val m =>
      if h : idx < k.size then
        match m.get? k[idx] with
        | none   => none
        | some t => loop t (idx + 1)
      else
        val
  loop t 0

/-- Returns the value of the longest key in `t` that is a prefix of `k`, if any. -/
@[inline]
partial def findLongestPrefix? (cmp : α → α → Ordering) (t : PrefixTreeNode α β cmp) (k : Array α) : Option β :=
  let rec @[specialize] loop acc? (node : PrefixTreeNode α β cmp) (idx : Nat) :=
    match node with
    | .Node val m =>
      if h : idx < k.size then
        match m.get? k[idx] with
        | none   => val
        | some t => loop (val <|> acc?) t (idx + 1)
      else
        val <|> acc?
  loop none t 0

@[inline]
partial def foldMatchingM [Monad m] (cmp : α → α → Ordering) (t : PrefixTreeNode α β cmp) (k : Array α) (init : σ) (f : β → σ → m σ) : m σ :=
  let rec @[specialize] fold : PrefixTreeNode α β cmp → σ → m σ
    | PrefixTreeNode.Node b? n, d => do
      let d ← match b? with
        | none   => pure d
        | some b => f b d
      n.foldlM (init := d) fun d _ t => fold t d
  let rec @[specialize] find (idx : Nat) (node : PrefixTreeNode α β cmp) (d : σ) : m σ :=
    if h : idx < k.size then
      match node with
      | PrefixTreeNode.Node _ m =>
        match m.get? k[idx] with
        | none   => pure init
        | some t => find (idx + 1) t d
    else
      fold node d
  find 0 t init

inductive WellFormed (cmp : α → α → Ordering) : PrefixTreeNode α β cmp → Prop where
  | emptyWff  : WellFormed cmp empty
  | insertWff : WellFormed cmp t → WellFormed cmp (insert cmp t k val)

end PrefixTreeNode

@[expose] def PrefixTree (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Type (max u v) :=
  { t : PrefixTreeNode α β cmp // t.WellFormed cmp }

open PrefixTreeNode

def PrefixTree.empty : PrefixTree α β p :=
  ⟨PrefixTreeNode.empty, WellFormed.emptyWff⟩

instance : Inhabited (PrefixTree α β p) where
  default := PrefixTree.empty

instance : EmptyCollection (PrefixTree α β p) where
  emptyCollection := PrefixTree.empty

@[inline]
def PrefixTree.insert (t : PrefixTree α β p) (k : Array α) (v : β) : PrefixTree α β p :=
  ⟨t.val.insert p k v, WellFormed.insertWff t.property⟩

@[inline]
def PrefixTree.find? (t : PrefixTree α β p) (k : Array α) : Option β :=
  t.val.find? p k

@[inline, inherit_doc PrefixTreeNode.findLongestPrefix?]
def PrefixTree.findLongestPrefix? (t : PrefixTree α β p) (k : Array α) : Option β :=
  t.val.findLongestPrefix? p k

@[inline]
def PrefixTree.foldMatchingM [Monad m] (t : PrefixTree α β p) (k : Array α) (init : σ) (f : β → σ → m σ) : m σ :=
  t.val.foldMatchingM p k init f

@[inline]
def PrefixTree.foldM [Monad m] (t : PrefixTree α β p) (init : σ) (f : β → σ → m σ) : m σ :=
  t.foldMatchingM #[] init f

@[inline]
def PrefixTree.forMatchingM [Monad m] (t : PrefixTree α β p) (k : Array α) (f : β → m Unit) : m Unit :=
  t.val.foldMatchingM p k () (fun b _ => f b)

@[inline]
def PrefixTree.forM [Monad m] (t : PrefixTree α β p) (f : β → m Unit) : m Unit :=
  t.forMatchingM #[] f

end Lean
