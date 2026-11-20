module

import Lean.Fmt.Util.RangeTree
meta import Lean.Fmt.Util.RangeTree

/-!
Tests the utilities backing the auto-formatter's range tree: `binSearchRightmost`,
`binSearchLeftmost`, `compareRanges` and `RangeTree`.
-/

open Lean Lean.Fmt

-- Helper to create a Syntax.Range
def mkRange (start stop : Nat) : Syntax.Range :=
  { start := ⟨start⟩, stop := ⟨stop⟩ }

/-! ## Tests for binSearchRightmost -/

-- Empty array returns none
#guard (binSearchRightmost #[] 5 id (· < ·)).isNone

-- Single element array - exact match
#guard (binSearchRightmost #[5] 5 id (· < ·) == some (0, 5))

-- Single element array - query larger than element (returns element)
#guard (binSearchRightmost #[5] 10 id (· < ·) == some (0, 5))

-- Single element array - query smaller than element (returns none)
#guard (binSearchRightmost #[5] 3 id (· < ·)).isNone

-- Multiple elements - exact match at end
#guard (binSearchRightmost #[1, 3, 5, 7, 9] 9 id (· < ·) == some (4, 9))

-- Multiple elements - exact match at start
#guard (binSearchRightmost #[1, 3, 5, 7, 9] 1 id (· < ·) == some (0, 1))

-- Multiple elements - exact match in middle
#guard (binSearchRightmost #[1, 3, 5, 7, 9] 5 id (· < ·) == some (2, 5))

-- Multiple elements - query between elements (returns next smaller)
#guard (binSearchRightmost #[1, 3, 5, 7, 9] 6 id (· < ·) == some (2, 5))

-- Multiple elements - query larger than all (returns last)
#guard (binSearchRightmost #[1, 3, 5, 7, 9] 100 id (· < ·) == some (4, 9))

-- Multiple elements - query smaller than all (returns none)
#guard (binSearchRightmost #[1, 3, 5, 7, 9] 0 id (· < ·)).isNone

-- Duplicate elements - returns rightmost
#guard (binSearchRightmost #[1, 3, 3, 3, 5] 3 id (· < ·) == some (3, 3))

-- With key function - search by first element of pair
#guard (binSearchRightmost #[(1, "a"), (3, "b"), (5, "c")] 3 (·.1) (· < ·) == some (1, (3, "b")))

-- With key function - query between elements
#guard (binSearchRightmost #[(1, "a"), (3, "b"), (5, "c")] 4 (·.1) (· < ·) == some (1, (3, "b")))

/-! ## Tests for binSearchLeftmost -/

-- Empty array returns none
#guard (binSearchLeftmost #[] 5 id (· < ·)).isNone

-- Single element array - exact match
#guard (binSearchLeftmost #[5] 5 id (· < ·) == some (0, 5))

-- Single element array - query smaller than element (returns element)
#guard (binSearchLeftmost #[5] 3 id (· < ·) == some (0, 5))

-- Single element array - query larger than element (returns none)
#guard (binSearchLeftmost #[5] 10 id (· < ·)).isNone

-- Multiple elements - exact match at end
#guard (binSearchLeftmost #[1, 3, 5, 7, 9] 9 id (· < ·) == some (4, 9))

-- Multiple elements - exact match at start
#guard (binSearchLeftmost #[1, 3, 5, 7, 9] 1 id (· < ·) == some (0, 1))

-- Multiple elements - exact match in middle
#guard (binSearchLeftmost #[1, 3, 5, 7, 9] 5 id (· < ·) == some (2, 5))

-- Multiple elements - query between elements (returns next larger)
#guard (binSearchLeftmost #[1, 3, 5, 7, 9] 4 id (· < ·) == some (2, 5))

-- Multiple elements - query smaller than all (returns first)
#guard (binSearchLeftmost #[1, 3, 5, 7, 9] 0 id (· < ·) == some (0, 1))

-- Multiple elements - query larger than all (returns none)
#guard (binSearchLeftmost #[1, 3, 5, 7, 9] 100 id (· < ·)).isNone

-- Duplicate elements - returns leftmost
#guard (binSearchLeftmost #[1, 3, 3, 3, 5] 3 id (· < ·) == some (1, 3))

-- With key function - search by first element of pair
#guard (binSearchLeftmost #[(1, "a"), (3, "b"), (5, "c")] 3 (·.1) (· < ·) == some (1, (3, "b")))

-- With key function - query between elements
#guard (binSearchLeftmost #[(1, "a"), (3, "b"), (5, "c")] 2 (·.1) (· < ·) == some (1, (3, "b")))

/-! ## Tests for compareRanges -/

-- Disjoint ranges - first comes before second
#guard compareRanges (mkRange 0 5) (mkRange 10 15) == .lt

-- Disjoint ranges - second comes before first
#guard compareRanges (mkRange 10 15) (mkRange 0 5) == .gt

-- Equal ranges
#guard compareRanges (mkRange 5 10) (mkRange 5 10) == .eq

-- First contains second (first is larger, should be less)
#guard compareRanges (mkRange 0 20) (mkRange 5 15) == .lt

-- Second contains first (second is larger, should be greater)
#guard compareRanges (mkRange 5 15) (mkRange 0 20) == .gt

-- Same start, first is larger
#guard compareRanges (mkRange 0 20) (mkRange 0 10) == .lt

-- Same start, second is larger
#guard compareRanges (mkRange 0 10) (mkRange 0 20) == .gt

-- Overlapping but neither contains the other - compare by start
#guard compareRanges (mkRange 0 10) (mkRange 5 15) == .lt
#guard compareRanges (mkRange 5 15) (mkRange 0 10) == .gt

/-! ## Tests for RangeTree.ofHashMap and RangeTree.findSmallestRangeContaining? -/

-- Empty HashMap yields empty tree
#guard (RangeTree.ofHashMap (α := Unit) {}).roots.isEmpty

-- Single entry
def singleEntry : Std.HashMap Syntax.Range String :=
  ({} : Std.HashMap _ _).insert (mkRange 0 10) "a"

#guard (RangeTree.ofHashMap singleEntry).roots.size == 1

-- Query exact match
#guard (RangeTree.ofHashMap singleEntry).findSmallestRangeContaining? (mkRange 0 10) == some (mkRange 0 10, "a")

-- Query contained range
#guard (RangeTree.ofHashMap singleEntry).findSmallestRangeContaining? (mkRange 2 8) == some (mkRange 0 10, "a")

-- Query outside range returns none
#guard (RangeTree.ofHashMap singleEntry).findSmallestRangeContaining? (mkRange 20 30) |>.isNone

-- Query overlapping but not contained returns none
#guard (RangeTree.ofHashMap singleEntry).findSmallestRangeContaining? (mkRange 5 15) |>.isNone

-- Nested entries - should find smallest containing range
def nestedEntries : Std.HashMap Syntax.Range String :=
  ({} : Std.HashMap _ _)
    |>.insert (mkRange 0 100) "outer"
    |>.insert (mkRange 10 50) "middle"
    |>.insert (mkRange 20 30) "inner"

def nestedTree := RangeTree.ofHashMap nestedEntries

-- Query inside innermost
#guard nestedTree.findSmallestRangeContaining? (mkRange 22 28) == some (mkRange 20 30, "inner")

-- Query inside middle but outside inner
#guard nestedTree.findSmallestRangeContaining? (mkRange 12 18) == some (mkRange 10 50, "middle")

-- Query inside outer but outside middle
#guard nestedTree.findSmallestRangeContaining? (mkRange 60 70) == some (mkRange 0 100, "outer")

-- Query exact match on inner
#guard nestedTree.findSmallestRangeContaining? (mkRange 20 30) == some (mkRange 20 30, "inner")

-- Disjoint entries
def disjointEntries : Std.HashMap Syntax.Range String :=
  ({} : Std.HashMap _ _)
    |>.insert (mkRange 0 10) "first"
    |>.insert (mkRange 20 30) "second"
    |>.insert (mkRange 40 50) "third"

def disjointTree := RangeTree.ofHashMap disjointEntries

#guard disjointTree.roots.size == 3

-- Query in first range
#guard disjointTree.findSmallestRangeContaining? (mkRange 2 8) == some (mkRange 0 10, "first")

-- Query in second range
#guard disjointTree.findSmallestRangeContaining? (mkRange 22 28) == some (mkRange 20 30, "second")

-- Query in third range
#guard disjointTree.findSmallestRangeContaining? (mkRange 42 48) == some (mkRange 40 50, "third")

-- Query between ranges returns none
#guard disjointTree.findSmallestRangeContaining? (mkRange 12 18) |>.isNone

-- Complex tree with multiple nested hierarchies
def complexEntries : Std.HashMap Syntax.Range String :=
  ({} : Std.HashMap _ _)
    |>.insert (mkRange 0 50) "left-outer"
    |>.insert (mkRange 10 40) "left-inner"
    |>.insert (mkRange 100 150) "right-outer"
    |>.insert (mkRange 110 140) "right-inner"
    |>.insert (mkRange 120 130) "right-innermost"

def complexTree := RangeTree.ofHashMap complexEntries

-- Query in left hierarchy
#guard complexTree.findSmallestRangeContaining? (mkRange 15 35) == some (mkRange 10 40, "left-inner")
#guard complexTree.findSmallestRangeContaining? (mkRange 5 8) == some (mkRange 0 50, "left-outer")

-- Query in right hierarchy
#guard complexTree.findSmallestRangeContaining? (mkRange 122 128) == some (mkRange 120 130, "right-innermost")
#guard complexTree.findSmallestRangeContaining? (mkRange 112 118) == some (mkRange 110 140, "right-inner")
#guard complexTree.findSmallestRangeContaining? (mkRange 102 108) == some (mkRange 100 150, "right-outer")

-- Query between left and right returns none
#guard complexTree.findSmallestRangeContaining? (mkRange 60 70) |>.isNone

-- Test with sibling ranges at same level
def siblingEntries : Std.HashMap Syntax.Range String :=
  ({} : Std.HashMap _ _)
    |>.insert (mkRange 0 100) "parent"
    |>.insert (mkRange 10 30) "child1"
    |>.insert (mkRange 40 60) "child2"
    |>.insert (mkRange 70 90) "child3"

def siblingTree := RangeTree.ofHashMap siblingEntries

-- Each child should be found
#guard siblingTree.findSmallestRangeContaining? (mkRange 15 25) == some (mkRange 10 30, "child1")
#guard siblingTree.findSmallestRangeContaining? (mkRange 45 55) == some (mkRange 40 60, "child2")
#guard siblingTree.findSmallestRangeContaining? (mkRange 75 85) == some (mkRange 70 90, "child3")

-- Gap between children should return parent
#guard siblingTree.findSmallestRangeContaining? (mkRange 32 38) == some (mkRange 0 100, "parent")

-- Zero-width ranges
def zeroWidthEntries : Std.HashMap Syntax.Range String :=
  ({} : Std.HashMap _ _)
    |>.insert (mkRange 0 10) "container"
    |>.insert (mkRange 5 5) "point"

def zeroWidthTree := RangeTree.ofHashMap zeroWidthEntries

-- Query the zero-width range itself
#guard zeroWidthTree.findSmallestRangeContaining? (mkRange 5 5) == some (mkRange 5 5, "point")

-- Adjacent ranges (non-overlapping)
def adjacentEntries : Std.HashMap Syntax.Range String :=
  ({} : Std.HashMap _ _)
    |>.insert (mkRange 0 10) "first"
    |>.insert (mkRange 10 20) "second"

def adjacentTree := RangeTree.ofHashMap adjacentEntries

#guard adjacentTree.findSmallestRangeContaining? (mkRange 2 8) == some (mkRange 0 10, "first")
#guard adjacentTree.findSmallestRangeContaining? (mkRange 12 18) == some (mkRange 10 20, "second")
