module

import Std.Data.HashMap
import Init.Util

/-!
Tests the flat linear-probing representation of `DHashMap`, including allocation-free value cells,
wrapped collision clusters, deletion from the middle of a cluster, resizing, dependent values, bulk
operations, and iteration.
-/

open Std

structure CollisionKey where
  id : Nat
  deriving Repr

instance : BEq CollisionKey where
  beq a b := a.id == b.id

instance : LawfulBEq CollisionKey where
  eq_of_beq := by
    rintro ⟨a⟩ ⟨b⟩ h
    have : a = b := of_decide_eq_true h
    cases this
    rfl
  rfl := by simp [BEq.beq]

instance : Hashable CollisionKey where
  hash _ := 7

def check (what : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw <| IO.userError s!"check failed: {what}"

def countKeys (xs : Array (NOption CollisionKey)) : Nat :=
  xs.foldl (fun n x => match x with | .none => n | .some _ => n + 1) 0

def countValues (xs : Array (NOption (NSigma fun _ : CollisionKey => Nat))) : Nat :=
  xs.foldl (fun n x => match x with | .none => n | .some _ => n + 1) 0

def checkFlatRepresentation (m : HashMap CollisionKey Nat) : IO Unit := do
  let raw := m.1.1
  check "parallel arrays have equal sizes" (raw.keyArray.size == raw.valueArray.size)
  check "key markers cover every live value" (countKeys raw.keyArray >= raw.size)
  check "value occupancy equals cached size" (countValues raw.valueArray == raw.size)

@[noinline] unsafe def checkFlatValueStorage (payload : Array Nat) : IO Unit := do
  let m : HashMap CollisionKey (Array Nat) :=
    (HashMap.emptyWithCapacity 1).insert (CollisionKey.mk 0) payload
  let mut found := false
  for cell in m.1.1.valueArray do
    match cell with
    | .none => pure ()
    | .some value =>
      found := true
      check "value cell adds no indirection" (ptrAddrUnsafe payload == ptrAddrUnsafe value)
      check "extracting a value adds no indirection"
        (ptrAddrUnsafe payload == ptrAddrUnsafe value.snd)
  check "inserted value has an occupied cell" found

def checkCapacityHint : IO Unit := do
  let m : HashMap CollisionKey Nat := .emptyWithCapacity 1
  let cells := m.1.1.keyArray.size
  let m := m.insert (CollisionKey.mk 0) 0
  check "capacity one is presized for one insertion" (m.1.1.keyArray.size == cells)
  let m : HashMap CollisionKey Nat := .emptyWithCapacity 2
  let cells := m.1.1.keyArray.size
  let m := m.insert (CollisionKey.mk 0) 0 |>.insert (CollisionKey.mk 1) 1
  check "capacity two is presized for two insertions" (m.1.1.keyArray.size == cells)

def checkCollisionCluster : IO Unit := do
  let keys := (List.range 12).map CollisionKey.mk
  let m := keys.foldl (init := HashMap.emptyWithCapacity 1)
    (fun m k => m.insert k (k.id * 10))
  checkFlatRepresentation m
  check "resized collision table" (m.1.1.keyArray.size > 1)
  for k in keys do
    check s!"lookup after wrapped insertion {k.id}" (m[k]? == some (k.id * 10))
  let m := m.erase (CollisionKey.mk 4)
  check "erased key is absent" (m[CollisionKey.mk 4]? == none)
  for k in keys.drop 5 do
    check s!"lookup beyond erased cluster cell {k.id}" (m[k]? == some (k.id * 10))
  let m := m.insert (CollisionKey.mk 7) 999 |>.insert (CollisionKey.mk 20) 200
  check "replace inside cluster" (m[CollisionKey.mk 7]? == some 999)
  check "reuse cluster after erase" (m[CollisionKey.mk 20]? == some 200)
  let cells := m.1.1.keyArray.size
  let m := m.insert (CollisionKey.mk 7) 1000
  check "replacement does not resize" (m.1.1.keyArray.size == cells)
  checkFlatRepresentation m
  let markerCount := countKeys m.1.1.keyArray
  let mut m := m
  for i in List.range 64 do
    m := (m.erase (CollisionKey.mk 7)).insert (CollisionKey.mk 7) i
  check "insertion reuses the first tombstone" (countKeys m.1.1.keyArray == markerCount)
  check "reused tombstone remains searchable" (m[CollisionKey.mk 7]? == some 63)

def DepValue (k : CollisionKey) := Fin (k.id + 1)

def checkDependentValues : IO Unit := do
  let m : DHashMap CollisionKey DepValue := DHashMap.emptyWithCapacity 1
  let m := m.insert (CollisionKey.mk 0)
    (show DepValue (CollisionKey.mk 0) from ⟨0, by decide⟩)
  let m := m.insert (CollisionKey.mk 3)
    (show DepValue (CollisionKey.mk 3) from ⟨2, by decide⟩)
  let m := m.insert (CollisionKey.mk 8)
    (show DepValue (CollisionKey.mk 8) from ⟨7, by decide⟩)
  check "dependent lookup before erase"
    ((m.get? (CollisionKey.mk 8)).map Fin.val == some 7)
  let m := m.erase (CollisionKey.mk 3)
  check "dependent lookup beyond erased cell"
    ((m.get? (CollisionKey.mk 8)).map Fin.val == some 7)
  let m := m.modify (CollisionKey.mk 8) fun _ => ⟨8, by decide⟩
  check "dependent modify" ((m.get? (CollisionKey.mk 8)).map Fin.val == some 8)
  let m := m.alter (CollisionKey.mk 0) fun _ => none
  check "dependent alter erase" (m.get? (CollisionKey.mk 0)).isNone

def checkBulkOperations : IO Unit := do
  let left : HashMap CollisionKey Nat :=
    .ofList [(⟨0⟩, 10), (⟨1⟩, 11), (⟨2⟩, 12), (⟨3⟩, 13)]
  let right : HashMap CollisionKey Nat :=
    .ofList [(⟨2⟩, 22), (⟨3⟩, 23), (⟨4⟩, 24), (⟨5⟩, 25)]
  let union := left ∪ right
  check "union prefers right" (union[CollisionKey.mk 2]? == some 22)
  check "union retains disjoint key" (union[CollisionKey.mk 0]? == some 10)
  let inter := left ∩ right
  check "intersection retains common key" (inter[CollisionKey.mk 3]? == some 13)
  check "intersection removes disjoint key" (inter[CollisionKey.mk 1]? == none)
  let diff := left \ right
  check "difference retains left-only key" (diff[CollisionKey.mk 1]? == some 11)
  check "difference removes common key" (diff[CollisionKey.mk 2]? == none)
  let filtered := union.filter fun k _ => k.id % 2 == 0
  check "filter keeps matching key" (filtered[CollisionKey.mk 4]? == some 24)
  check "filter removes nonmatching key" (filtered[CollisionKey.mk 5]? == none)
  let mapped := filtered.map fun _ v => v + 1
  check "map updates value" (mapped[CollisionKey.mk 4]? == some 25)
  let filterMapped := union.filterMap fun k v => if k.id < 3 then some (v + 100) else none
  check "filterMap updates retained value" (filterMapped[CollisionKey.mk 2]? == some 122)
  check "filterMap removes rejected value" (filterMapped[CollisionKey.mk 3]? == none)
  checkFlatRepresentation union
  checkFlatRepresentation inter
  checkFlatRepresentation diff

def checkIteration : IO Unit := do
  let m : HashMap CollisionKey Nat :=
    (List.range 10).foldl (init := {}) fun m i => m.insert ⟨i⟩ i
  let mut seen : Array Bool := Array.replicate 10 false
  for (k, v) in m.iter do
    check "iterator pairs keys and values" (k.id == v)
    seen := seen.set! k.id true
  check "iterator visits every occupied cell" (seen.all id)
  check "fold visits every occupied cell" (m.fold (fun n _ _ => n + 1) 0 == m.size)

public unsafe def main : IO Unit := do
  checkFlatValueStorage #[10, 20, 30, 40]
  checkCapacityHint
  checkCollisionCluster
  checkDependentValues
  checkBulkOperations
  checkIteration
  IO.println "ok"
