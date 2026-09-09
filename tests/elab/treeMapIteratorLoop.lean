module

import Std.Data.DTreeMap.Iterator
import Std.Data.TreeMap.Raw.Iterator
import Std.Data.TreeMap.Slice
import Std.Data.TreeSet.Raw.Iterator
import Std.Data.TreeSet.Raw.Slice

/-!
Tests that all tree map iterator implementations support loop-based consumers.
-/

open Std Std.Iterators

example {α : Type u} {β : α → Type v} {m : Type (max u v) → Type w} [Monad m] :
    IteratorLoop (DTreeMap.Internal.Zipper α β) Id m :=
  inferInstance

example {α : Type u} {β : α → Type v} {m : Type (max u v) → Type w} [Monad m] :
    LawfulIteratorLoop (DTreeMap.Internal.Zipper α β) Id m :=
  inferInstance

example {α : Type u} {β : α → Type v} [Ord α]
    {m : Type (max u v) → Type w} [Monad m] :
    IteratorLoop (DTreeMap.Internal.RxcIterator α β) Id m :=
  inferInstance

example {α : Type u} {β : α → Type v} [Ord α]
    {m : Type (max u v) → Type w} [Monad m] :
    LawfulIteratorLoop (DTreeMap.Internal.RxcIterator α β) Id m :=
  inferInstance

example {α : Type u} {β : α → Type v} [Ord α]
    {m : Type (max u v) → Type w} [Monad m] :
    IteratorLoop (DTreeMap.Internal.RxoIterator α β) Id m :=
  inferInstance

example {α : Type u} {β : α → Type v} [Ord α]
    {m : Type (max u v) → Type w} [Monad m] :
    LawfulIteratorLoop (DTreeMap.Internal.RxoIterator α β) Id m :=
  inferInstance

private def dTreeMap : DTreeMap Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: 12 -/
#guard_msgs in
#eval Id.run do
  let mut sum := 0
  for entry in dTreeMap.iter do
    sum := sum + entry.2
  return sum

private def dTreeMapRaw : DTreeMap.Raw Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: (12, 6, 12) -/
#guard_msgs in
#eval Id.run do
  let mut entrySum := 0
  for entry in dTreeMapRaw.iter do
    entrySum := entrySum + entry.2
  let mut keySum := 0
  for key in dTreeMapRaw.keysIter do
    keySum := keySum + key
  let mut valueSum := 0
  for value in dTreeMapRaw.valuesIter do
    valueSum := valueSum + value
  return (entrySum, keySum, valueSum)

private def treeMap : TreeMap Nat Nat :=
  .ofList [(1, 2), (2, 4), (3, 6)]

/-- info: 6 -/
#guard_msgs in
#eval Id.run do
  let mut sum := 0
  for (_, value) in treeMap[*...=2].iter do
    sum := sum + value
  return sum

private def treeMapRaw : TreeMap.Raw Nat Nat :=
  .ofList [(1, 2), (2, 4), (3, 6)]

/-- info: (12, 6, 12) -/
#guard_msgs in
#eval Id.run do
  let mut entrySum := 0
  for (_, value) in treeMapRaw.iter do
    entrySum := entrySum + value
  let mut keySum := 0
  for key in treeMapRaw.keysIter do
    keySum := keySum + key
  let mut valueSum := 0
  for value in treeMapRaw.valuesIter do
    valueSum := valueSum + value
  return (entrySum, keySum, valueSum)

private def treeSet : TreeSet.Raw Nat :=
  .ofList [1, 2, 3]

/-- info: 6 -/
#guard_msgs in
#eval Id.run do
  let mut sum := 0
  for value in treeSet.iter do
    sum := sum + value
  return sum

/-- info: 3 -/
#guard_msgs in
#eval Id.run do
  let mut sum := 0
  for value in treeSet[*...<3].iter do
    sum := sum + value
  return sum
