import Std.Data.HashSet

/-!
Tests that `HashSet.markLinear` and `HashSet.Raw.markLinear` preserve the semantics of the set they
mark and that the marker survives the bucket array reallocation that insertion performs once the set
outgrows its capacity.
-/

open Std

def build (n : Nat) : HashSet Nat := Id.run do
  -- Deliberately starts far below `n` so that the set has to resize several times.
  let mut s := (HashSet.emptyWithCapacity 1).markLinear
  for i in 0...n do
    s := s.insert i
  return s

def shrink (n : Nat) : HashSet Nat := Id.run do
  let mut s := (build n).markLinear
  for i in 0...n do
    if i % 2 == 0 then
      s := s.erase i
  return s

def buildRaw (n : Nat) : HashSet.Raw Nat := Id.run do
  let mut s := (HashSet.Raw.emptyWithCapacity 1).markLinear
  for i in 0...n do
    s := s.insert i
  return s

def shrinkRaw (n : Nat) : HashSet.Raw Nat := Id.run do
  let mut s := (buildRaw n).markLinear
  for i in 0...n do
    if i % 2 == 0 then
      s := s.erase i
  return s

/--
Two separately marked sets must stay separate: if closed term extraction or common sub-expression
elimination shared them, the insertions below would abort.
-/
def pair : Nat × Nat :=
  let s₁ := (HashSet.emptyWithCapacity 8).markLinear
  let s₂ := (HashSet.emptyWithCapacity 8).markLinear
  ((s₁.insert 0).size, (s₂.insert 1).size)

def main : IO Unit := do
  let s := build 100
  IO.println s.size
  IO.println (s.contains 7)
  IO.println (s.contains 100)
  let s := shrink 100
  IO.println s.size
  IO.println (s.contains 7)
  IO.println (s.contains 8)
  let s := buildRaw 100
  IO.println s.size
  IO.println (s.contains 7)
  let s := shrinkRaw 100
  IO.println s.size
  IO.println (s.contains 7)
  IO.println (s.contains 8)
  IO.println pair
