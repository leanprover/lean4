module

import Std.Data.HashMap.Iterator

/-!
Tests that all hash map iterators can be consumed by `for` loops.
-/

open Std

private def dHashMapRaw : DHashMap.Raw Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: (12, 6, 12) -/
#guard_msgs in
#eval Id.run do
  let mut entrySum := 0
  for entry in dHashMapRaw.iter do
    entrySum := entrySum + entry.2
  let mut keySum := 0
  for key in dHashMapRaw.keysIter do
    keySum := keySum + key
  let mut valueSum := 0
  for value in dHashMapRaw.valuesIter do
    valueSum := valueSum + value
  return (entrySum, keySum, valueSum)

private def dHashMap : DHashMap Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: (12, 6, 12) -/
#guard_msgs in
#eval Id.run do
  let mut entrySum := 0
  for entry in dHashMap.iter do
    entrySum := entrySum + entry.2
  let mut keySum := 0
  for key in dHashMap.keysIter do
    keySum := keySum + key
  let mut valueSum := 0
  for value in dHashMap.valuesIter do
    valueSum := valueSum + value
  return (entrySum, keySum, valueSum)

private def hashMapRaw : HashMap.Raw Nat Nat :=
  .ofList [(1, 2), (2, 4), (3, 6)]

/-- info: (12, 6, 12) -/
#guard_msgs in
#eval Id.run do
  let mut entrySum := 0
  for (_, value) in hashMapRaw.iter do
    entrySum := entrySum + value
  let mut keySum := 0
  for key in hashMapRaw.keysIter do
    keySum := keySum + key
  let mut valueSum := 0
  for value in hashMapRaw.valuesIter do
    valueSum := valueSum + value
  return (entrySum, keySum, valueSum)

private def hashMap : HashMap Nat Nat :=
  .ofList [(1, 2), (2, 4), (3, 6)]

/-- info: (12, 6, 12) -/
#guard_msgs in
#eval Id.run do
  let mut entrySum := 0
  for (_, value) in hashMap.iter do
    entrySum := entrySum + value
  let mut keySum := 0
  for key in hashMap.keysIter do
    keySum := keySum + key
  let mut valueSum := 0
  for value in hashMap.valuesIter do
    valueSum := valueSum + value
  return (entrySum, keySum, valueSum)
