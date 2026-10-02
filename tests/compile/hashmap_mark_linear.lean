import Std.Data.HashMap

/-!
Tests that `HashMap.markLinear` preserves the semantics of the map it marks and that the marker
survives the bucket array reallocation that insertion performs once the map outgrows its capacity.
-/

open Std

def build (n : Nat) : HashMap Nat Nat := Id.run do
  -- Deliberately starts far below `n` so that the map has to resize several times.
  let mut m := (HashMap.emptyWithCapacity 1).markLinear
  for i in 0...n do
    m := m.insert i (i * i)
  return m

def shrink (n : Nat) : HashMap Nat Nat := Id.run do
  let mut m := (build n).markLinear
  for i in 0...n do
    if i % 2 == 0 then
      m := m.erase i
  return m

/--
Two separately marked maps must stay separate: if closed term extraction or common sub-expression
elimination shared them, the insertions below would abort.
-/
def pair : Nat × Nat :=
  let m₁ := (HashMap.emptyWithCapacity 8).markLinear
  let m₂ := (HashMap.emptyWithCapacity 8).markLinear
  ((m₁.insert 0 0).size, (m₂.insert 1 1).size)

def main : IO Unit := do
  let m := build 100
  IO.println m.size
  IO.println (m.get? 7)
  IO.println (m.get? 100)
  let m := shrink 100
  IO.println m.size
  IO.println (m.get? 7)
  IO.println (m.get? 8)
  IO.println pair
