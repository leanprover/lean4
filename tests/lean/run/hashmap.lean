import Std.Data.HashSet.Basic
import Std.Data.HashSet.Raw
import Std.Data.HashMap.AdditionalOperations

open Std

/-! Basic tests for (DHashMap|HashMap|HashSet)(.Raw)? functions which do not (yet) have proofs -/

namespace DHashMap.Raw

def m : DHashMap.Raw Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: [⟨2, 8⟩] -/
#guard_msgs in
#eval (m.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨1, none⟩, ⟨2, some 8⟩, ⟨3, none⟩] -/
#guard_msgs in
#eval (m.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨3, 6⟩] -/
#guard_msgs in
#eval (m.filter fun _ v => v > 4).toList

def addValueToStateAndAddKey (acc : Nat) (k : Nat) (v : Nat) : StateM Nat Nat := do
  modify (fun st => st + v)
  return acc + k

/-- info: (18, 25) -/
#guard_msgs in
#eval (m.foldM (init := 12) addValueToStateAndAddKey).run 13

/-- info: 18 -/
#guard_msgs in
#eval m.fold (init := 12) fun acc k _ => acc + k

def addValueToState (_ : Nat) (v : Nat) : StateM Nat PUnit := do
  modify (fun st => st + v)

/-- info: ((), 25) -/
#guard_msgs in
#eval (m.forM addValueToState).run 13

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for ⟨k, v⟩ in m do
    ans := (k, v) :: ans
  return ans

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval m.toList

/-- info: #[⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval m.toArray

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DHashMap.Raw.Const.toList m

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DHashMap.Raw.Const.toArray m

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval m.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval m.keysArray

/-- info: [2, 4, 6] -/
#guard_msgs in
#eval m.values

/-- info: [⟨16, 9⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval (m.insertMany [⟨16, 8⟩, ⟨16, 9⟩]).toList

/-- info: [⟨16, 9⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval (DHashMap.Raw.Const.insertMany m [(16, 8), (16, 9)]).toList

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval (DHashMap.Raw.Const.ofList [(1, 2), (2, 4), (3, 6)]).toList

/-- info: Std.DHashMap.Raw.ofList [⟨1, 4⟩] -/
#guard_msgs in
#eval DHashMap.Raw.Const.ofList [(1, 2), (1, 4)]

end DHashMap.Raw

namespace DHashMap

def m : DHashMap Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: [⟨2, 8⟩] -/
#guard_msgs in
#eval (m.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨1, none⟩, ⟨2, some 8⟩, ⟨3, none⟩] -/
#guard_msgs in
#eval (m.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨3, 6⟩] -/
#guard_msgs in
#eval (m.filter fun _ v => v > 4).toList

def addValueToStateAndAddKey (acc : Nat) (k : Nat) (v : Nat) : StateM Nat Nat := do
  modify (fun st => st + v)
  return acc + k

/-- info: (18, 25) -/
#guard_msgs in
#eval (m.foldM (init := 12) addValueToStateAndAddKey).run 13

/-- info: 18 -/
#guard_msgs in
#eval m.fold (init := 12) fun acc k _ => acc + k

def addValueToState (_ : Nat) (v : Nat) : StateM Nat PUnit := do
  modify (fun st => st + v)

/-- info: ((), 25) -/
#guard_msgs in
#eval (m.forM addValueToState).run 13

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for ⟨k, v⟩ in m do
    ans := (k, v) :: ans
  return ans

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval m.toList

/-- info: #[⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval m.toArray

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DHashMap.Const.toList m

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DHashMap.Const.toArray m

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval m.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval m.keysArray

/-- info: [2, 4, 6] -/
#guard_msgs in
#eval m.values

/-- info: [⟨16, 9⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval (m.insertMany [⟨16, 8⟩, ⟨16, 9⟩]).toList

/-- info: [⟨16, 9⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval (DHashMap.Const.insertMany m [(16, 8), (16, 9)]).toList

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval (DHashMap.Const.ofList [(1, 2), (2, 4), (3, 6)]).toList

/-- info: Std.DHashMap.ofList [⟨1, 4⟩] -/
#guard_msgs in
#eval DHashMap.Const.ofList [(1, 2), (1, 4)]

end DHashMap

namespace HashMap.Raw

def m : HashMap.Raw Nat Nat :=
  .ofList [(1, 2), (2, 4), (3, 6)]

/-- info: [(2, 8)] -/
#guard_msgs in
#eval (m.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(1, none), (2, some 8), (3, none)] -/
#guard_msgs in
#eval (m.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(3, 6)] -/
#guard_msgs in
#eval (m.filter fun _ v => v > 4).toList

def addValueToStateAndAddKey (acc : Nat) (k : Nat) (v : Nat) : StateM Nat Nat := do
  modify (fun st => st + v)
  return acc + k

/-- info: (18, 25) -/
#guard_msgs in
#eval (m.foldM (init := 12) addValueToStateAndAddKey).run 13

/-- info: 18 -/
#guard_msgs in
#eval m.fold (init := 12) fun acc k _ => acc + k

def addValueToState (_ : Nat) (v : Nat) : StateM Nat PUnit := do
  modify (fun st => st + v)

/-- info: ((), 25) -/
#guard_msgs in
#eval (m.forM addValueToState).run 13

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for (k, v) in m do
    ans := (k, v) :: ans
  return ans

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.toList

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.toArray

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval m.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval m.keysArray

/-- info: [2, 4, 6] -/
#guard_msgs in
#eval m.values

/-- info: [(16, 9), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval (m.insertMany [(16, 8), (16, 9)]).toList

/-- info: Std.HashMap.Raw.ofList [(1, 4)] -/
#guard_msgs in
#eval HashMap.Raw.ofList [(1, 2), (1, 4)]

end HashMap.Raw

namespace HashMap

def m : HashMap Nat Nat :=
  .ofList [(1, 2), (2, 4), (3, 6)]

/-- info: [(2, 8)] -/
#guard_msgs in
#eval (m.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(1, none), (2, some 8), (3, none)] -/
#guard_msgs in
#eval (m.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(3, 6)] -/
#guard_msgs in
#eval (m.filter fun _ v => v > 4).toList

def addValueToStateAndAddKey (acc : Nat) (k : Nat) (v : Nat) : StateM Nat Nat := do
  modify (fun st => st + v)
  return acc + k

/-- info: (18, 25) -/
#guard_msgs in
#eval (m.foldM (init := 12) addValueToStateAndAddKey).run 13

/-- info: 18 -/
#guard_msgs in
#eval m.fold (init := 12) fun acc k _ => acc + k

def addValueToState (_ : Nat) (v : Nat) : StateM Nat PUnit := do
  modify (fun st => st + v)

/-- info: ((), 25) -/
#guard_msgs in
#eval (m.forM addValueToState).run 13

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for (k, v) in m do
    ans := (k, v) :: ans
  return ans

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.toList

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.toArray

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval m.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval m.keysArray

/-- info: [2, 4, 6] -/
#guard_msgs in
#eval m.values

/-- info: [(16, 9), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval (m.insertMany [(16, 8), (16, 9)]).toList

/-- info: Std.HashMap.ofList [(1, 4)] -/
#guard_msgs in
#eval HashMap.ofList [(1, 2), (1, 4)]

/-- info: Std.HashMap.ofList [(1, 2), (2, 4), (3, 6), (4, 5), (37, 37)] -/
#guard_msgs in
#eval m ∪ {(4, 5), (37, 37)}

/-- info: Std.HashMap.ofList [(1, 3), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.modify 1 (fun v => v + 1)

/-- info: Std.HashMap.ofList [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.modify 4 (fun v => v + 1)

/-- info: Std.HashMap.ofList [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.alter 4 (fun v? => v?.map (· + 2))

/-- info: Std.HashMap.ofList [(1, 2), (2, 4), (3, 6), (4, 7)] -/
#guard_msgs in
#eval m.alter 4 (fun _ => some 7)

/-- info: Std.HashMap.ofList [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.alter 4 (fun _ => none)

/-- info: Std.HashMap.ofList [(1, 2), (2, 4)] -/
#guard_msgs in
#eval m.alter 3 (fun _ => none)

/-- info: Std.HashMap.ofList [(1, 2), (2, 4), (3, 37)] -/
#guard_msgs in
#eval m.alter 3 (fun _ => some 37)

end HashMap

namespace HashSet.Raw

def m : HashSet.Raw Nat :=
  .ofList [1, 2, 1000000000]

/-- info: [1000000000] -/
#guard_msgs in
#eval (m.filter fun v => v > 4).toList

def addKeyToStateAndAddKey (acc : Nat) (k : Nat) : StateM Nat Nat := do
  modify (fun st => st + k)
  return acc + k

/-- info: (1000000015, 1000000016) -/
#guard_msgs in
#eval (m.foldM (init := 12) addKeyToStateAndAddKey).run 13

/-- info: 1000000015 -/
#guard_msgs in
#eval m.fold (init := 12) fun acc k => acc + k

def addKeyToState (k : Nat) : StateM Nat PUnit := do
  modify (fun st => st + k)

/-- info: ((), 1000000016) -/
#guard_msgs in
#eval (m.forM addKeyToState).run 13

/-- info: [1000000000, 2, 1] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List Nat := []
  for k in m do
    ans := k :: ans
  return ans

/-- info: true -/
#guard_msgs in
#eval m.any fun x => x > 4

/-- info: false -/
#guard_msgs in
#eval m.any fun x => x = 0

/-- info: true -/
#guard_msgs in
#eval m.all fun x => x < 2^30

/-- info: false -/
#guard_msgs in
#eval m.all fun x => x > 4

/-- info: [1, 2, 1000000000] -/
#guard_msgs in
#eval m.toList

/-- info: #[1, 2, 1000000000] -/
#guard_msgs in
#eval m.toArray

/-- info: Std.HashSet.Raw.ofList [16, 1, 2, 1000000000] -/
#guard_msgs in
#eval m ∪ {16, 16}

/-- info: [16, 1, 2, 1000000000] -/
#guard_msgs in
#eval (m.insertMany [16, 16]).toList

/-- info: Std.HashSet.Raw.ofList [1, 100] -/
#guard_msgs in
#eval HashSet.Raw.ofList [1, 100]

end HashSet.Raw

namespace HashSet

def m : HashSet Nat :=
  .ofList [1, 2, 1000000000]

/-- info: [1000000000] -/
#guard_msgs in
#eval (m.filter fun v => v > 4).toList

def addKeyToStateAndAddKey (acc : Nat) (k : Nat) : StateM Nat Nat := do
  modify (fun st => st + k)
  return acc + k

/-- info: (1000000015, 1000000016) -/
#guard_msgs in
#eval (m.foldM (init := 12) addKeyToStateAndAddKey).run 13

/-- info: 1000000015 -/
#guard_msgs in
#eval m.fold (init := 12) fun acc k => acc + k

def addKeyToState (k : Nat) : StateM Nat PUnit := do
  modify (fun st => st + k)

/-- info: ((), 1000000016) -/
#guard_msgs in
#eval (m.forM addKeyToState).run 13

/-- info: [1000000000, 2, 1] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List Nat := []
  for k in m do
    ans := k :: ans
  return ans

/-- info: true -/
#guard_msgs in
#eval m.any fun x => x > 4

/-- info: false -/
#guard_msgs in
#eval m.any fun x => x = 0

/-- info: true -/
#guard_msgs in
#eval m.all fun x => x < 2^30

/-- info: false -/
#guard_msgs in
#eval m.all fun x => x > 4

/-- info: [1, 2, 1000000000] -/
#guard_msgs in
#eval m.toList

/-- info: #[1, 2, 1000000000] -/
#guard_msgs in
#eval m.toArray

/-- info: Std.HashSet.ofList [16, 1, 2, 1000000000] -/
#guard_msgs in
#eval m ∪ {16, 16}

/-- info: [16, 1, 2, 1000000000] -/
#guard_msgs in
#eval (m.insertMany [16, 16]).toList

/-- info: Std.HashSet.ofList [1, 100] -/
#guard_msgs in
#eval HashSet.ofList [1, 100]

end HashSet
