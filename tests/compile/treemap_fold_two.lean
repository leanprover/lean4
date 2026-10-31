module

import Std.Data.TreeMap
import Std.Data.ExtTreeMap
import Std.Data.ExtDTreeMap
import Std.Data.TreeMap.Raw
import Std.Data.DTreeMap.Raw

/-! Joint tree folds visit the comparator union once, in order, with distinct value types,
the left stored key on collisions, and no calls with both values absent. -/

private def check (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError "incorrect joint tree fold"

public def main : IO Unit := do
  let left := Std.TreeMap.ofList [(1, 10), (3, 30)]
  let right := Std.TreeMap.ofList [(2, "two"), (3, "three"), (4, "four")]
  let result := left.foldl₂ (fun acc k a b => acc.push (k, a, b)) #[] right
  check (result == #[(1, some 10, none), (2, none, some "two"),
    (3, some 30, some "three"), (4, none, some "four")])
  let cmp := compareOn (fun (k : Nat × Nat) => k.1)
  let left := Std.ExtTreeMap.ofList [((1, 10), 100), ((3, 30), 300)] cmp
  let right := Std.ExtTreeMap.ofList [((2, 20), "two"), ((3, 31), "three")] cmp
  let result := left.foldl₂ (fun acc k a b => acc.push (k, a, b)) #[] right
  check (result == #[((1, 10), some 100, none), ((2, 20), none, some "two"),
    ((3, 30), some 300, some "three")])
  let left : Std.DTreeMap Nat (Vector Nat) := (∅ : Std.DTreeMap Nat (Vector Nat)).insert 1 #v[10]
  let right : Std.DTreeMap Nat (Vector String) :=
    (∅ : Std.DTreeMap Nat (Vector String)).insert 1 #v["one"]
  let result := left.foldl₂ (fun acc k a b => acc.push (k, a.map (·.toList), b.map (·.toList))) #[] right
  check (result == #[(1, some [10], some ["one"])])
  for n in [0, 1, 10, 1000] do
    let left := Std.TreeMap.ofList ((List.range n).map fun k => (2 * k, k))
    let right := Std.TreeMap.ofList ((List.range n).map fun k => (2 * k + 1, toString k))
    let result := left.foldl₂ (fun acc k _ _ => acc.push k) #[] right
    check (result == (List.range (2 * n)).toArray)
  let rawLeft := Std.TreeMap.Raw.ofList [(1, 10), (3, 30)]
  let rawRight := Std.TreeMap.Raw.ofList [(2, "two"), (3, "three")]
  check (rawLeft.foldl₂ (fun acc k _ _ => acc.push k) #[] rawRight == #[1, 2, 3])
  let extLeft : Std.ExtDTreeMap Nat (Vector Nat) :=
    (∅ : Std.ExtDTreeMap Nat (Vector Nat)).insert 1 #v[10]
  let extRight : Std.ExtDTreeMap Nat (Vector String) :=
    (∅ : Std.ExtDTreeMap Nat (Vector String)).insert 1 #v["one"]
  let events := extLeft.foldl₂
    (fun acc k a b => acc.push (k, a.map (·.toList), b.map (·.toList))) #[] extRight
  check (events == #[(1, some [10], some ["one"])])
  let badLeft : Std.DTreeMap.Raw Nat (fun _ => Nat) :=
    ⟨.inner 0 1 10 .leaf (.inner 0 3 30 .leaf .leaf)⟩
  let badRight : Std.DTreeMap.Raw Nat (fun _ => String) :=
    ⟨.inner 0 2 "two" .leaf (.inner 0 4 "four" .leaf .leaf)⟩
  let events := Std.DTreeMap.Raw.Const.foldl₂ (fun acc k a b => acc.push (k, a, b))
    #[] badLeft badRight
  check (events == #[(1, some 10, none), (2, none, some "two"),
    (3, some 30, none), (4, none, some "four")])
