module

import Std.Data.HashMap
import Std.Data.ExtHashMap
import Std.Data.ExtDHashMap
import Std.Data.HashMap.Raw
import Std.Data.DHashMap.Raw

/-! Hash-map collision merging, including deletion, weak key equality, constant hashes,
dependent values, malformed raw maps, and linear use of destination maps and values. -/

private structure Key where
  id : Nat
  rep : Nat

private instance : BEq Key := ⟨fun a b => a.id == b.id⟩
private instance : Hashable Key := ⟨fun _ => 0⟩
private instance : EquivBEq Key where
  rfl := by intro a; exact (BEq.rfl : (a.id == a.id) = true)
  symm := by
    intro a b h
    change (a.id == b.id) = true at h
    change (b.id == a.id) = true
    exact BEq.symm h
  trans := by
    intro a b c hab hbc
    change (a.id == b.id) = true at hab
    change (b.id == c.id) = true at hbc
    change (a.id == c.id) = true
    exact BEq.trans hab hbc
private instance : LawfulHashable Key where
  hash_eq _ _ _ := rfl

private def check (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError "incorrect hash-map merge"

-- Keep calls with constant arguments from becoming shared closed terms.
@[never_extract]
private def buildArrays (n : Nat) (offset := 0) : Std.HashMap Nat (Array Nat) := Id.run do
  let mut out := (Std.HashMap.emptyWithCapacity 1).markLinear
  for i in 0...n do
    let k := offset + i
    out := out.insert k (#[k].markLinear)
  return out

private def constantHash : IO Unit :=
  letI : Hashable Nat := ⟨fun _ => 0⟩
  do
    let collisionLeft : Std.HashMap Nat Nat := Std.HashMap.ofList ((List.range 100).map fun k => (k, k + 100))
    let collisionRight : Std.HashMap Nat Nat := Std.HashMap.ofList ((List.range 200).map fun k => (k, k))
    let collisionResult := collisionLeft.mergeWith? (fun k a b => if k % 2 == 0 then none else some (a - b)) collisionRight
    check (collisionResult.size == 150)
    for k in 0...200 do
      check (collisionResult[k]? == if k < 100 then (if k % 2 == 0 then none else some 100) else some k)
    let extLeft := Std.ExtHashMap.ofList [(1, 10), (2, 20), (4, 40)]
    let extRight := Std.ExtHashMap.ofList [(1, 10), (3, 30), (4, 4)]
    let extLeft' := Std.ExtHashMap.ofList [(4, 40), (2, 20), (1, 10)]
    let extRight' := Std.ExtHashMap.ofList [(4, 4), (3, 30), (1, 10)]
    let f (_ : Nat) (a b : Nat) := if a == b then none else some (a - b)
    check (extLeft.mergeWith? f extRight == extLeft'.mergeWith? f extRight')


public def main : IO Unit := do
  let left := Std.HashMap.ofList [(1, 10), (2, 20)]
  let right := Std.HashMap.ofList [(1, 10), (2, 3), (3, 30)]
  let result := left.mergeWith? (fun _ a b => if a == b then none else some (a - b)) right
  check (result.size == 2 && result[1]? == none && result[2]? == some 17 && result[3]? == some 30)
  let result := left.mergeWith (fun _ a b => a - b) right
  check (result.size == 3 && result[1]? == some 0 && result[2]? == some 17)
  let left := Std.HashMap.ofList [(Key.mk 1 10, 100), (Key.mk 2 20, 200)]
  let right := Std.HashMap.ofList [(Key.mk 1 11, 3), (Key.mk 3 30, 300)]
  let result := left.mergeWith? (fun k a b => some (a - b + k.rep)) right
  check (result[Key.mk 1 0]? == some 108)
  check ((result.getKey? (Key.mk 1 0)).map (·.rep) == some 11)
  check ((result.getKey? (Key.mk 2 0)).map (·.rep) == some 20)
  let extLeft := Std.ExtHashMap.ofList [(Key.mk 1 10, 100)]
  let extRight := Std.ExtHashMap.ofList [(Key.mk 1 11, 3)]
  let extResult := extLeft.mergeWith? (fun k a b => some (a - b + k.rep)) extRight
  check (extResult[Key.mk 1 0]? == some 108)
  check ((extResult.getKey? (Key.mk 1 0)).map (·.rep) == some 11)
  let left := buildArrays 1 99
  let right := Std.HashMap.ofList ((List.range 100).map fun k => (k, #[2 * k]))
  let result := left.mergeWith? (fun _ a b => some (a.push b[0]!)) right
  check (result.size == 100 && result[99]? == some #[99, 198])
  let left := buildArrays 100
  let right := Std.HashMap.ofList [(1, #[7])]
  let result := left.mergeWith (fun _ a b => a.push b[0]!) right
  check (result.size == 100 && result[1]? == some #[1, 7])
  let depLeft : Std.DHashMap Nat (Vector Nat) := (∅ : Std.DHashMap Nat (Vector Nat)).insert 1 #v[10]
  let depRight : Std.DHashMap Nat (Vector Nat) := (∅ : Std.DHashMap Nat (Vector Nat)).insert 1 #v[3]
  check (((depLeft.mergeWith? (fun _ a b => some (a.zipWith (· - ·) b)) depRight).get? 1) ==
    some #v[7])
  let rawDepLeft : Std.DHashMap.Raw Nat (Vector Nat) :=
    (∅ : Std.DHashMap.Raw Nat (Vector Nat)).insert 1 #v[10]
  let rawDepRight : Std.DHashMap.Raw Nat (Vector Nat) :=
    (∅ : Std.DHashMap.Raw Nat (Vector Nat)).insert 1 #v[3]
  check (((rawDepLeft.mergeWith? (fun _ a b => some (a.zipWith (· - ·) b)) rawDepRight).get? 1) ==
    some #v[7])
  let extDepLeft : Std.ExtDHashMap Nat (Vector Nat) := ∅
  let extDepRight : Std.ExtDHashMap Nat (Vector Nat) :=
    (∅ : Std.ExtDHashMap Nat (Vector Nat)).insert 1 #v[3]
  check (((extDepLeft.mergeWith (fun _ a _ => a) extDepRight).get? 1) == some #v[3])
  let bad : Std.HashMap.Raw Nat Nat := ⟨⟨0, #[]⟩⟩
  let good := Std.HashMap.Raw.ofList [(1, 7)]
  check ((bad.mergeWith? (fun _ _ _ => none) good)[1]? == some 7)
  check ((good.mergeWith? (fun _ _ _ => none) bad)[1]? == some 7)
  constantHash
