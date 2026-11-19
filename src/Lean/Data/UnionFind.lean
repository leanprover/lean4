/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Init.Data.Array.Basic
import Init.Data.Bool
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Consumers.Monadic.Loop

/-!
This module provides a basic UnionFind data structure for managing equivalence classes based on
`Nat` identifiers. We expect that elements of equivalence classes are managed externally via some
additional mapping data structure.
-/

namespace Lean

structure UnionFind.Node where
  parent : Nat
  rank : Nat
  next : Nat
  deriving Inhabited

public structure UnionFind where
  private arr : Array UnionFind.Node

namespace UnionFind

public def emptyWithCapacity (n : Nat) : UnionFind :=
  ⟨Array.emptyWithCapacity n⟩

public instance : EmptyCollection UnionFind where
  emptyCollection := emptyWithCapacity 0

public instance : Inhabited UnionFind where
  default := {}

@[inline]
public def markLinear (uf : UnionFind) : UnionFind :=
  ⟨uf.arr.markLinear⟩

@[inline]
public def size (uf : UnionFind) : Nat := uf.arr.size

@[inline]
public def push (uf : UnionFind) : UnionFind × Nat :=
  let newNode := uf.arr.size
  ⟨⟨uf.arr.push ⟨newNode, 0, newNode⟩⟩, newNode⟩

@[inline]
def node (uf : UnionFind) (node : Nat) : UnionFind.Node :=
  uf.arr[node]!

@[inline]
def parent (uf : UnionFind) (node : Nat) : Nat :=
  uf.node node |>.parent

@[inline]
def rank (uf : UnionFind) (node : Nat) : Nat :=
  uf.node node |>.rank

@[inline]
public def next (uf : UnionFind) (node : Nat) : Nat :=
  uf.node node |>.next

public partial def find! (uf : UnionFind) (eqc : Nat) : UnionFind × Nat :=
  let parent := uf.parent eqc
  if parent == eqc then
    (uf, eqc)
  else
    let parentParent := uf.parent parent
    let uf : UnionFind := ⟨uf.arr.modify eqc fun n => { n with parent := parentParent }⟩
    uf.find! parent

public def union! (uf : UnionFind) (eqc1 eqc2 : Nat) : UnionFind :=
  let (uf, root1) := uf.find! eqc1
  let (uf, root2) := uf.find! eqc2
  if root1 == root2 then
    uf
  else
    let root1Rank := uf.rank root1
    let root1Next := uf.next root1
    let root2Rank := uf.rank root2
    let root2Next := uf.next root2
    let arr := uf.arr
    if root1Rank < root2Rank then
      let arr := arr.modify root1 fun n => { n with parent := root2, next := root2Next }
      let arr := arr.modify root2 fun n => { n with next := root1Next }
      ⟨arr⟩
    else
      let offset := Bool.toNat <| root1Rank == root2Rank
      let arr := arr.modify root2 fun n => { n with parent := root1, next := root1Next }
      let arr := arr.modify root1 fun n => { n with rank := n.rank + offset, next := root2Next }
      ⟨arr⟩

public partial def root! (uf : UnionFind) (eqc : Nat) : Nat :=
  let parent := uf.parent eqc
  if eqc != parent then
    uf.root! parent
  else
    eqc

public def checkEquiv! (uf : UnionFind) (eqc1 eqc2 : Nat) : UnionFind × Bool :=
  let (uf, root1) := uf.find! eqc1
  let (uf, root2) := uf.find! eqc2
  (uf, root1 == root2)

public structure UnionFindIter where
  uf : UnionFind
  start : Nat
  current : Nat
  first : Bool

public instance [Pure m] : Std.Iterator UnionFindIter m Nat where
  IsPlausibleStep _ _ := True
  step it := pure <| .deflate <|
    let curr := it.internalState.current
    if curr == it.internalState.start then
      if it.internalState.first then
        .yield { it with internalState.first := false, internalState.current := it.internalState.uf.next curr} curr trivial
      else
        .done trivial
    else
      .yield { it with internalState.current := it.internalState.uf.next curr } curr trivial

public instance [Pure m] [Monad n] : Std.IteratorLoop UnionFindIter m n :=
  .defaultImplementation

public def iterClassM (uf : UnionFind) (eqc : Nat) (m : Type → Type w') :
    Std.IterM (α := UnionFindIter) m Nat :=
  ⟨{ uf, start := eqc, current := eqc, first := true }⟩

public def iterClass (uf : UnionFind) (eqc : Nat) : Std.Iter (α := UnionFindIter) Nat :=
  (uf.iterClassM eqc Id).toIter

end UnionFind

end Lean
