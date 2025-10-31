/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Syntax
public import Init.While
public import Init.Data.Array.QSort.Basic

namespace Lean.Fmt

/--
Binary searches a `query` in an array `xs` that is sorted according to `lt`.
Both `query` and elements of `xs` are compared after applying `key`.

Yields the rightmost index of any found value that is contained in `xs` several times.
If `query` is not contained in `xs`, yields the next smaller value and index, or `none` if there
is no next smaller value.
-/
public def binSearchRightmost (xs : Array α) (query : β) (key : α → β) (lt : β → β → Bool)
    : Option (Nat × α) := do
  let mut l := 0
  let mut r := xs.size
  while l < r do
    let m := l + (r - l) / 2
    let some v := xs[m]?
      | unreachable!
    if lt query (key v) then
      r := m
    else
      l := m + 1
  let i := r - 1
  let v ← xs[i]?
  guard <| !(lt query (key v)) -- key v <= query
  return (i, v)

/--
Binary searches a `query` in an array `xs` that is sorted according to `lt`.
Both `query` and elements of `xs` are compared after applying `key`.

Yields the leftmost index of any found value that is contained in `xs` several times.
If `query` is not contained in `xs`, yields the next larger value and index, or `none` if there
is no next larger value.
-/
public def binSearchLeftmost (xs : Array α) (query : β) (key : α → β) (lt : β → β → Bool)
    : Option (Nat × α) := do
  let mut l := 0
  let mut r := xs.size
  while l < r do
    let m := l + (r - l) / 2
    let some v := xs[m]?
      | unreachable!
    if lt (key v) query then
      l := m + 1
    else
      r := m
  let i := l
  let v ← xs[i]?
  guard <| !(lt (key v) query) -- query <= key v
  return (i, v)

public structure RangeTreeNode (α : Type) where
  -- Invariants:
  -- - All `range`s in the subtrees of `children` are contained in the `range` of this node.
  -- - The `range`s of the immediate `children` are disjoint.
  -- - `children` is sorted ascendingly by start position and end position of the `range`
  --   of each child.
  range : Syntax.Range
  value : α
  children : Array (RangeTreeNode α)
deriving Inhabited, Repr

public structure RangeTree (α : Type) where
  -- Invariants:
  -- - The `range`s of the `roots` are disjoint.
  -- - `roots` is sorted ascendingly by start position and end position of the `range`
  --   of each root.
  roots : Array (RangeTreeNode α)
deriving Inhabited, Repr

/--
Compares two ranges `a` and `b`.
If `a` and `b` are disjoint, yields which of the two ranges starts and ends first.
If `a` is contained in `b` or `b` is contained in `a`, yields which of the two ranges is larger.
If `a` and `b` are overlapping (but one is not contained in the other one), yields which of the two
ranges starts first.
-/
public def compareRanges (a b : Syntax.Range) : Ordering :=
  Ord.compare a.start.byteIdx b.start.byteIdx |>.then (Ord.compare b.stop.byteIdx a.stop.byteIdx)

/--
Creates a new `RangeTree` for efficient range queries for the given `entries`.
The ranges in `entries` must all either be disjoint or contain one another;
they cannot overlap without containing one another.
This invariant is generally fulfilled for ranges of the same `Syntax`.
-/
public partial def RangeTree.ofHashMap [Inhabited α] (entries : Std.HashMap Syntax.Range α)
    : RangeTree α := Id.run do
  let entries := entries.toArray.qsort (fun (a, _) (b, _) => compareRanges a b == .lt)
  let mut roots := #[]
  let mut i := 0
  while true do
    let (i', some root) := go entries i
      | break
    i := i'
    roots := roots.push root
  return ⟨roots⟩
where
  go (entries : Array (Syntax.Range × α)) (i : Nat) : Nat × Option (RangeTreeNode α) := Id.run do
    let some (range, value) := entries[i]?
      | (i, none)
    let mut children : Array (RangeTreeNode α) := #[]
    let mut i := i + 1
    while entries[i]?.any (fun (childRange, _) => range.includes childRange) do
      let (i', childNode?) := go entries i
      i := i'
      if let some childNode := childNode? then
        children := children.push childNode
    return (i, some ⟨range, value, children⟩)

/--
Finds the smallest range and its associated value in `t` that contains `range`,
or yields `none` if no range in `t` contains `range`.
-/
public partial def RangeTree.findSmallestRangeContaining?
    [Inhabited α] (t : RangeTree α) (range : Syntax.Range)
    : Option (Syntax.Range × α) := do
  let child ← findChildContaining t.roots range
  go child
where
  go (t : RangeTreeNode α) : Option (Syntax.Range × α) := do
    guard <| t.range.includes range
    let some child := findChildContaining t.children range
      | return (t.range, t.value)
    let some childMatch := go child
      | return (t.range, t.value)
    return childMatch
  findChildContaining (children : Array (RangeTreeNode α)) (range : Syntax.Range)
      : Option (RangeTreeNode α) :=
    binSearchRightmost children range (·.range) (·.start < ·.start) |>.map (·.2)
