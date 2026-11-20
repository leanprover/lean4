import Lean.Data.Iterators.Producers.PersistentArray
import Std.Data.Iterators

/-!
Tests the `PersistentArray` iterators `iter`, `iterFromIdx` and `revIter`, including arrays large
enough to have several levels of inner nodes, and start indices in the trie, at node boundaries and
in the tail.
-/

open Lean

def range (n : Nat) : PersistentArray Nat := Id.run do
  let mut a : PersistentArray Nat := {}
  for i in *...n do
    a := a.push i
  return a

/-- info: [] -/
#guard_msgs in
#eval (range 0).iter.toList

/-- info: [] -/
#guard_msgs in
#eval (range 0).revIter.toList

/-- info: [] -/
#guard_msgs in
#eval ((range 0).iterFromIdx 3).toList

/-- info: [0, 1, 2, 3, 4] -/
#guard_msgs in
#eval (range 5).iter.toList

/-- info: [4, 3, 2, 1, 0] -/
#guard_msgs in
#eval (range 5).revIter.toList

/-- info: [2, 3, 4] -/
#guard_msgs in
#eval ((range 5).iterFromIdx 2).toList

/-- info: [] -/
#guard_msgs in
#eval ((range 5).iterFromIdx 7).toList

/-- info: #[33, 34, 35] -/
#guard_msgs in
#eval ((range 36).iterFromIdx 33).toArray

/-- info: 45 -/
#guard_msgs in
#eval Id.run do
  let mut sum := 0
  for x in (range 10).iter do
    sum := sum + x
  return sum

-- Early exit through `return` stops the traversal.
def firstAbove (a : PersistentArray Nat) (k : Nat) : Option Nat := Id.run do
  for x in a.iter do
    if x > k then
      return some x
  return none

/-- info: some 1001 -/
#guard_msgs in
#eval firstAbove (range 5000) 1000

/-- info: true -/
#guard_msgs in
#eval (range 3000).iter.any (· == 2999)

/-- info: [9, 7, 5, 3, 1] -/
#guard_msgs in
#eval (range 10).revIter.filter (· % 2 == 1) |>.toList

/-
Compare against `toList` for sizes around the leaf size (32), the size of a two-level trie
(32 * 32 + 32) and a three-level trie, and for start indices on and around node boundaries.
-/
/-- info: true -/
#guard_msgs in
#eval Id.run do
  for n in [1, 31, 32, 33, 64, 65, 100, 1023, 1024, 1025, 1056, 1057, 2000, 33000, 33824, 33825,
      40000] do
    let a := range n
    let l := a.toList
    if a.iter.toList != l then return false
    if a.revIter.toList != l.reverse then return false
    for s in [0, 1, 2, 31, 32, 33, 500, 1023, 1024, 1025, 1100, 32768, 33000, 33792, 33800,
        n - 1, n, n + 1, n + 40] do
      if (a.iterFromIdx s).toList != l.drop s then return false
  return true

-- Arrays built by `pop` and `set` share structure with their originals.
/-- info: true -/
#guard_msgs in
#eval Id.run do
  let a := range 2000
  let b := (a.pop.pop.set 5 100).set 1500 7
  return b.iter.toList == b.toList && b.revIter.toList == b.toList.reverse &&
    (b.iterFromIdx 1200).toList == b.toList.drop 1200

-- `for` loops use a custom `IteratorLoop` instance; check early exit and loops in other monads.
def lastBelow (a : PersistentArray Nat) (k : Nat) : Option Nat := Id.run do
  for x in a.revIter do
    if x < k then
      return some x
  return none

/-- info: some 999 -/
#guard_msgs in
#eval lastBelow (range 5000) 1000

/-- info: (none, none) -/
#guard_msgs in
#eval (firstAbove (range 0) 0, lastBelow (range 0) 1)

/-- info: ([1056, 1057, 1058], [1058, 1057, 1056]) -/
#guard_msgs in
#eval
  let a := range 1059
  let go (it : List Nat → StateM (List Nat) Unit) : List Nat := (it [] |>.run [] |>.2).reverse
  (go fun _ => do for x in a.iterFromIdx 1056 do modify (x :: ·),
   go fun _ => do for x in a.revIter do if x < 1056 then break else modify (x :: ·))

/-- info: true -/
#guard_msgs in
#eval Id.run do
  for n in [0, 1, 32, 33, 1056, 1057, 33825] do
    let a := range n
    let mut fwd := #[]
    for x in a.iter do fwd := fwd.push x
    let mut bwd := #[]
    for x in a.revIter do bwd := bwd.push x
    if fwd.toList != a.toList || bwd.toList != a.toList.reverse then return false
    if a.iter.fold (· + ·) 0 != a.foldl (· + ·) 0 then return false
  return true
