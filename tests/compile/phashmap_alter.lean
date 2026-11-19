import Lean.Data.PersistentHashMap

open Lean Lean.PersistentHashMap

abbrev Map := PersistentHashMap Nat Nat

def expect (msg : String) (b : Bool) : IO Unit :=
  unless b do IO.println s!"FAIL: {msg}"

def expectEq [BEq α] [ToString α] (msg : String) (actual expected : α) : IO Unit :=
  unless actual == expected do
    IO.println s!"FAIL: {msg}: got {actual}, expected {expected}"

def main : IO Unit := do
  let m : Map := PersistentHashMap.empty
  let m := m.alter 1 fun _ => some 10
  expectEq "insert via alter" (m.find? 1) (some 10)
  let m := m.alter 1 fun v? => v?.map (· + 100)
  expectEq "update via alter" (m.find? 1) (some 110)
  let m := m.alter 1 fun _ => none
  expectEq "delete via alter" (m.find? 1) none
  expect "delete empties map" m.isEmpty

  let m : Map := (PersistentHashMap.empty.insert 1 10).insert 2 20
  let m := m.alter 3 fun _ => none
  expectEq "no-op absent: 1" (m.find? 1) (some 10)
  expectEq "no-op absent: 2" (m.find? 2) (some 20)
  expectEq "no-op absent: 3" (m.find? 3) none

  let m : Map := PersistentHashMap.empty.insert 1 10
  let m := m.alter (1 + 32) fun _ => none
  expectEq "no-op different-key same-slot: 1 preserved" (m.find? 1) (some 10)
  expectEq "no-op different-key same-slot: other absent" (m.find? (1 + 32)) none

  let max := PersistentHashMap.maxDepth.toNat
  let keys := [1, 32^5 + 1, 32^max + 1, 32^(max+1) + 1, 32^(max+2) + 1]
  let m : Map := keys.zipIdx.foldl (init := PersistentHashMap.empty)
    fun m (k, i) => m.alter k fun _ => some (i + 1)
  for (k, i) in keys.zipIdx do
    expectEq s!"deep find {k}" (m.find? k) (some (i + 1))
  expectEq "deep max depth" m.stats.maxDepth max
  expect "collisions present" (m.stats.numCollisions > 0)

  let m := keys.foldl (init := m) fun m k => m.alter k fun v? => v?.map (· + 1000)
  for (k, i) in keys.zipIdx do
    expectEq s!"deep update {k}" (m.find? k) (some (i + 1 + 1000))

  let m := keys.foldl (init := m) fun m k => m.alter k fun _ => none
  for k in keys do
    expectEq s!"deep delete {k}" (m.find? k) none
  expect "fully drained" m.isEmpty

  let mAlter : Map := (List.range 200).foldl (init := PersistentHashMap.empty)
    fun m i => m.alter i fun _ => some (i * 10)
  let mInsert : Map := (List.range 200).foldl (init := PersistentHashMap.empty)
    fun m i => m.insert i (i * 10)
  for i in 0...200 do
    expectEq s!"alter vs insert at {i}" (mAlter.find? i) (mInsert.find? i)
  expectEq "alter stats vs insert: nodes" mAlter.stats.numNodes mInsert.stats.numNodes
  expectEq "alter stats vs insert: collisions" mAlter.stats.numCollisions mInsert.stats.numCollisions
  expectEq "alter stats vs insert: depth" mAlter.stats.maxDepth mInsert.stats.maxDepth

  IO.println "OK"
