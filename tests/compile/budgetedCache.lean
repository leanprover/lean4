module

import Lean
import Lean.Data.BudgetedCache

/-!
Tests the cache for #15985: hash collisions, replacement of keys and values, exhaustion eviction,
shared-pointer hits, persistent snapshots, and the collision-node paths of PersistentHashMap.
-/

open Lean

private structure Key where
  hashValue : UInt64
  id : Nat
  expr : Expr
  deriving Inhabited

private instance : Hashable Key := ⟨Key.hashValue⟩

private instance : BudgetedBEq Key where
  beq a b budget := do
    if a.id != b.id then return .false
    a.expr.equalBudgeted b.expr budget

private abbrev TestCache := BudgetedCache Key Nat

private def check (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw <| IO.userError msg

@[noinline] private def chain (n : Nat) : IO Expr := do
  let r ← IO.mkRef (mkBVar 0)
  for _ in [:n] do r.modify fun e => mkApp (mkConst `f) e
  r.get

private def lookup (c : TestCache) (key : Key) (budget : USize) : BaseIO (Option Nat × TestCache) :=
  (c.find? key set budget : StateT TestCache BaseIO (Option Nat)).run c

private def checkLayout (hashes : Array UInt64) : IO Unit := do
  let e₁ ← chain 32
  let e₂ ← chain 32
  let keys := hashes.mapIdx fun i h => Key.mk h i e₁
  let original := keys.foldl (init := ({} : TestCache)) fun c k => c.insert k k.id
  for k in keys do
    check ((← lookup original k 0).1 == some k.id) "pointer hit"
  let oldKey := keys[0]!
  let newKey := { oldKey with expr := e₂ }
  let (miss, evicted) ← lookup original newKey 8
  check miss.isNone "exhaustion must miss"
  check (← lookup evicted oldKey 0).1.isNone "exhaustion must erase the old key"
  check ((← lookup original oldKey 0).1 == some oldKey.id) "snapshot survives erasure"
  for k in keys[1:] do
    check ((← lookup evicted k 0).1 == some k.id) "erasure preserves neighboring hashes"
  let replaced := original.insert newKey 99
  check ((← lookup replaced newKey 0).1 == some 99) "insertion replaces both key and value"
  check ((← lookup original oldKey 0).1 == some oldKey.id) "snapshot survives replacement"
  let collision := { oldKey with id := 1000 }
  let (miss, retained) ← lookup original collision 0
  check miss.isNone "unequal keys with equal hashes must miss"
  check ((← lookup retained oldKey 0).1 == some oldKey.id) "inequality must retain the candidate"
  let replaced := retained.insert collision 1000
  check ((← lookup replaced collision 0).1 == some 1000) "hash collision replacement"
  check (← lookup replaced oldKey 0).1.isNone "old colliding key is gone"
  -- A recursive computation may insert another candidate after the caller's miss.
  let afterRecursiveCall := evicted.insert collision 1000
  let afterCallerInsert := afterRecursiveCall.insert newKey 99
  check ((← lookup afterCallerInsert newKey 0).1 == some 99) "insertion after recursive computation"

public def main : IO Unit := do
  for hashes in ([#[0], #[0, 32, 64], (Array.range 8).map (fun i => i.toUInt64.shiftLeft 5),
      (Array.range 8).map (fun i => i.toUInt64.shiftLeft 40)] : List (Array UInt64)) do
    checkLayout hashes
  let a ← chain 8
  let b ← chain 8
  let key := Key.mk 0 0 a
  let copy := Key.mk 0 0 b
  let c : TestCache := ({} : TestCache).insert key 42
  check ((← lookup c copy 8).1 == some 42) "small structural cache hit"
  let writes ← IO.mkRef 0
  let onEvict := fun (_ : TestCache) => writes.modify (· + 1)
  discard <| c.find? key onEvict 0
  discard <| c.find? { key with hashValue := 1 } onEvict 0
  discard <| c.find? { key with id := 1 } onEvict 0
  check ((← writes.get) == 0) "hits and ordinary misses must not update state"
  discard <| c.find? copy onEvict 0
  check ((← writes.get) == 1) "exhaustion must update state once"
