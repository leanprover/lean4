module

import Std.Data.TreeMap
import Std.Data.ExtTreeMap
import Std.Data.ExtDTreeMap
import Std.Data.TreeMap.Raw
import Std.Data.DTreeMap.Raw

/-! Deletion-capable tree merging: collision order, key representatives, dependent values,
raw and extensional wrappers, and exclusive ownership of left values. -/

private def collision (_ : Nat) (a b : Nat) : Option Nat :=
  if a == b then none else some (a - b)

example : ((Std.TreeMap.ofList [(1, 10), (2, 20)]).mergeWith? collision
    (Std.TreeMap.ofList [(1, 10), (2, 3), (3, 30)])).toList = [(2, 17), (3, 30)] := by
  decide +kernel

private def check (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError "incorrect deletion-capable tree merge"

public def main : IO Unit := do
  let left := Std.TreeMap.ofList [(1, (#[10] : Array Nat).markLinear)]
  let right := Std.TreeMap.ofList [(1, #[3]), (2, #[4])]
  let result := left.mergeWith? (fun _ a b => some (a.push b[0]!)) right
  check (result.toList == [(1, #[10, 3]), (2, #[4])])
  let cmp := compareOn (fun (k : Nat × Nat) => k.1)
  let left := Std.TreeMap.ofList [((1, 10), 100), ((2, 20), 200)] cmp
  let right := Std.TreeMap.ofList [((1, 11), 3), ((3, 30), 300)] cmp
  let result := left.mergeWith? (fun k a b => some (a - b + k.2)) right
  check (result.toList == [((1, 11), 108), ((2, 20), 200), ((3, 30), 300)])
  check (result.size == 3)
  let extLeft := Std.ExtTreeMap.ofList [((1, 10), 100)] cmp
  let extRight := Std.ExtTreeMap.ofList [((1, 11), 3)] cmp
  check ((extLeft.mergeWith? (fun k a b => some (a - b + k.2)) extRight).toList ==
    [((1, 11), 108)])
  let rawLeft := Std.TreeMap.Raw.ofList [(1, 10), (2, 20)]
  let rawRight := Std.TreeMap.Raw.ofList [(1, 10), (2, 3), (3, 30)]
  check ((rawLeft.mergeWith? collision rawRight).toList == [(2, 17), (3, 30)])
  let depLeft : Std.DTreeMap Nat (Vector Nat) := (∅ : Std.DTreeMap Nat (Vector Nat)).insert 1 #v[10]
  let depRight : Std.DTreeMap Nat (Vector Nat) := (∅ : Std.DTreeMap Nat (Vector Nat)).insert 1 #v[3]
  check (((depLeft.mergeWith? (fun _ a b => some (a.zipWith (· - ·) b)) depRight).get? 1) ==
    some #v[7])
  let extDepLeft : Std.ExtDTreeMap Nat (Vector Nat) := ∅
  let extDepRight : Std.ExtDTreeMap Nat (Vector Nat) := (∅ : Std.ExtDTreeMap Nat (Vector Nat)).insert 1 #v[3]
  check (((extDepLeft.mergeWith? (fun _ _ _ => none) extDepRight).get? 1) == some #v[3])
  let left := Std.TreeMap.ofList ((List.range 100).map fun k => (k, k))
  let right := Std.TreeMap.ofList ((List.range 100).map fun k => (k, k))
  let deleted := left.mergeWith? (fun _ _ _ => none) right
  check (deleted.isEmpty && deleted.size == 0 && deleted.toList.isEmpty)
  let depRawLeft : Std.DTreeMap.Raw Nat (Vector Nat) :=
    (∅ : Std.DTreeMap.Raw Nat (Vector Nat)).insert 1 #v[10]
  let depRawRight : Std.DTreeMap.Raw Nat (Vector Nat) :=
    (∅ : Std.DTreeMap.Raw Nat (Vector Nat)).insert 1 #v[3]
  check (((depRawLeft.mergeWith? (fun _ a b => some (a.zipWith (· - ·) b)) depRawRight).get? 1) ==
    some #v[7])
  for leftMask in List.range 16 do
    for rightMask in List.range 16 do
      let entries (mask offset : Nat) := (List.range 4).filterMap fun k =>
        if mask &&& (1 <<< k) != 0 then some (k, offset + k) else none
      let left := Std.TreeMap.ofList (entries leftMask 10)
      let right := Std.TreeMap.ofList (entries rightMask 3)
      let result := left.mergeWith?
        (fun k a b => if k % 2 == 0 then none else some (a - b)) right
      let expected := (List.range 4).filterMap fun k =>
        let l := leftMask &&& (1 <<< k) != 0
        let r := rightMask &&& (1 <<< k) != 0
        if l && r then (if k % 2 == 0 then none else some (k, 7))
        else if l then some (k, 10 + k)
        else if r then some (k, 3 + k)
        else none
      check (result.toList == expected && result.size == expected.length)
