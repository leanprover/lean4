/-
Copyright (c) 2024 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import Lean.Meta.DiscrTree.Basic
public section
namespace Lean.Meta.DiscrTree
namespace Trie

/-!
Accessors for traversals. They view `t` through `Trie.force`, which is free for `chain`, `node` and
`lazy`, but allocates when unfolding a `suffix`; traversals that need to be fast handle `suffix`
separately.
-/

/--
Generate a trie node from values and an array of children.
-/
@[inline]
def mkNode (vs : Array α) (cs : Array (Key × Trie α)) : Trie α :=
  if h : vs.isEmpty ∧ cs.size = 1 then
    .chain cs[0].1 cs[0].2
  else
    .node vs cs

/--
Inspect a trie node as an array of values and an array of children.
-/
@[inline]
def asNode (t : Trie α) : Array α × Array (Key × Trie α) :=
  match t.force with
  | ⟨.chain k v, _⟩ => ⟨#[], #[(k, v)]⟩
  | ⟨.node vs cs, _⟩ => ⟨vs, cs⟩

/--
Returns the values stored at the current trie node.
Equivalent to `t.asNode.1`.
-/
@[inline]
def nodeValues (t : Trie α) : Array α :=
  match t.force with
  | ⟨.chain _ _, _⟩ => #[]
  | ⟨.node vs _, _⟩ => vs

/--
Returns the child nodes of the current trie node.
Equivalent to `t.asNode.2`.
-/
@[inline]
def nodeChildren (t : Trie α) : Array (Key × Trie α) :=
  match t.force with
  | ⟨.chain k v, _⟩ => #[(k, v)]
  | ⟨.node _ cs, _⟩ => cs

/-- Whether the current trie node has children. -/
@[inline]
def hasChildren (t : Trie α) : Bool :=
  match t.force with
  | ⟨.chain .., _⟩ => true
  | ⟨.node _ cs, _⟩ => !cs.isEmpty

/-- Returns the child of the current trie node for `Key.star`, the minimal key. -/
@[inline]
def starChild? (t : Trie α) : Option (Trie α) :=
  match t.force with
  | ⟨.chain k c, _⟩ => if k == .star then some c else none
  | ⟨.node _ cs, _⟩ => if h : 0 < cs.size then (if cs[0].1 == .star then some cs[0].2 else none) else none

/-- Returns the child of the current trie node for `k`. -/
@[inline]
def findChild? (t : Trie α) (k : Key) : Option (Trie α) :=
  match t.force with
  | ⟨.chain k' c, _⟩ => if k' == k then some c else none
  | ⟨.node _ cs, _⟩ => (cs.binSearch (k, default) (fun a b => a.1 < b.1)).map (·.2)

/-- Monadically folds over the children of the current trie node. -/
@[inline]
def foldChildrenM [Monad m] (f : σ → Key → Trie α → m σ) (init : σ) (t : Trie α) : m σ :=
  match t.force with
  | ⟨.chain k c, _⟩ => f init k c
  | ⟨.node _ cs, _⟩ => cs.foldlM (init := init) fun s (k, c) => f s k c

/--
Checks whether a trie node is empty (no values and no children).

This is only a check for actual trie emptiness (`t.size = 0`) if all operations maintain the
invariant that no trie node has an empty child node.
-/
@[inline]
def isEmptyNode (t : Trie α) : Bool :=
  match t.force with
  | ⟨.chain _ _, _⟩ => false
  | ⟨.node vs children, _⟩ => vs.isEmpty && children.isEmpty

/--
Monadically fold the keys and values stored in a `Trie`.
-/
@[specialize]
partial def foldM [Monad m] (initialKeys : Array Key)
    (f : σ → Array Key → α → m σ) (init : σ) (t : Trie α) : m σ := do
  if let .suffix ks i v := t then
    return (← f init (initialKeys ++ ks.extract i ks.size) v)
  let s ← t.nodeValues.foldlM (init := init) fun s v => f s initialKeys v
  t.foldChildrenM (init := s) fun s k c => c.foldM (initialKeys.push k) f s

/--
Fold the keys and values stored in a `Trie`.
-/
@[inline]
def fold (initialKeys : Array Key) (f : σ → Array Key → α → σ) (init : σ) (t : Trie α) : σ :=
  Id.run <| t.foldM initialKeys (init := init) fun s k a => return f s k a

/--
Monadically fold the values stored in a `Trie`.
-/
@[specialize]
partial def foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : Trie α) : m σ := do
  if let .suffix _ _ v := t then
    return (← f init v)
  let s ← t.nodeValues.foldlM (init := init) f
  t.foldChildrenM (init := s) fun s _ c => c.foldValuesM (init := s) f

/--
Fold the values stored in a `Trie`.
-/
@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : Trie α) : σ :=
  Id.run <| t.foldValuesM (init := init) (pure <| f · ·)

/--
The number of values stored in a `Trie`.
-/
partial def size (t : Trie α) : Nat :=
  if let .suffix .. := t then 1
  else Id.run <| t.foldChildrenM (init := t.nodeValues.size) fun n _ c => n + size c

end Trie


/--
Monadically fold over the keys and values stored in a `DiscrTree`.
-/
@[inline]
def foldM [Monad m] (f : σ → Array Key → α → m σ) (init : σ)
    (t : DiscrTree α) : m σ :=
  t.root.foldlM (init := init) fun s k t => t.foldM #[k] (init := s) f

/--
Fold over the keys and values stored in a `DiscrTree`
-/
@[inline]
def fold (f : σ → Array Key → α → σ) (init : σ) (t : DiscrTree α) : σ :=
  Id.run <| t.foldM (init := init) fun s keys a => return f s keys a

/--
Monadically fold over the values stored in a `DiscrTree`.
-/
@[inline]
def foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : DiscrTree α) :
    m σ :=
  t.root.foldlM (init := init) fun s _ t => t.foldValuesM (init := s) f

/--
Fold over the values stored in a `DiscrTree`.
-/
@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : DiscrTree α) : σ :=
  Id.run <| t.foldValuesM (init := init) (pure <| f · ·)

/--
Check for the presence of a value satisfying a predicate.
-/
@[inline]
def containsValueP (t : DiscrTree α) (f : α → Bool) : Bool :=
  t.foldValues (init := false) fun r a => r || f a

/--
Extract the values stored in a `DiscrTree`.
-/
@[inline]
def values (t : DiscrTree α) : Array α :=
  t.foldValues (init := #[]) fun as a => as.push a

/--
Extract the keys and values stored in a `DiscrTree`.
-/
@[inline]
def toArray (t : DiscrTree α) : Array (Array Key × α) :=
  t.fold (init := #[]) fun as keys a => as.push (keys, a)

/--
Get the number of values stored in a `DiscrTree`. O(n) in the size of the tree.
-/
@[inline]
def size (t : DiscrTree α) : Nat :=
  t.root.foldl (init := 0) fun n _ t => n + t.size

variable {m : Type → Type} [Monad m]

/--
Apply a monadic function to the array of values at each node in a `DiscrTree`.
Any resulting subtrees containing no values will be pruned.
-/
@[specialize]
partial def Trie.mapArraysM (t : DiscrTree.Trie α) (f : Array α → m (Array β)) :
    m (DiscrTree.Trie β) :=
  match t with
  | .chain k c => do
    let vs ← f #[] -- Corner case. Possible future optimization: modify `mapArraysM` semantics to only call `f` for non-empty arrays and then eliminate this line
    let c ← c.mapArraysM f
    let cs := if c.isEmptyNode then #[] else #[(k, c)]
    return Trie.mkNode vs cs
  | .node vs children => do
    let vs ← f vs
    let children ← children.filterMapM fun (k, child) => do
      let child ← child.mapArraysM f
      if child.isEmptyNode then
        return none
      else
        return some (k, child)
    return Trie.mkNode vs children
  | t@(.lazy _) | t@(.suffix ..) => t.force.1.mapArraysM f

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
@[inline]
def mapArraysM (d : DiscrTree α) (f : Array α → m (Array β)) : m (DiscrTree β) := do
  let root ← d.root.mapM (fun t => t.mapArraysM f)
  pure { root := root.foldl (init := root) fun acc k t => if t.isEmptyNode then acc.erase k else acc }

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
@[inline]
def mapArrays (d : DiscrTree α) (f : Array α → Array β) : DiscrTree β :=
  Id.run <| d.mapArraysM fun A => pure (f A)

end Lean.Meta.DiscrTree
