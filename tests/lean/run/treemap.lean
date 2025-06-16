/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Std.Data.TreeSet.Basic
import Std.Data.TreeSet.Lemmas
import Std.Data.TreeSet.Raw.Basic
import Std.Data.DTreeMap.Raw.AdditionalOperations
import Std.Data.TreeMap.Raw.AdditionalOperations
import Std.Data.TreeMap.AdditionalOperations

open Std

variable {α : Type u} {β : Type v} [Ord α]

def mkDTreeMapSingleton (a : α) (b : β) : DTreeMap α (fun _ => β) := Id.run do
  let mut m : DTreeMap α (fun _ => β) := ∅
  m := m.insert a b
  return m

def mkTreeMapSingleton (a : α) (b : β) : TreeMap α β := Id.run do
  let mut m : TreeMap α β := ∅
  m := m.insert a b
  return m

def mkTreeSetSingleton (a : α) : TreeSet α := Id.run do
  let mut m : TreeSet α := ∅
  m := m.insert a
  return m

example [TransOrd α] [LawfulEqOrd α] (a : α) (b : β) : Option β :=
  mkDTreeMapSingleton a b |>.get? a

example [TransOrd α] [LawfulEqOrd α] (a : α) (b : β) : Option β :=
  (mkTreeMapSingleton a b)[a]?

example [TransOrd α] (a : α) (b : β) : (mkTreeMapSingleton a b).contains a := by
  simp [mkTreeMapSingleton, Id.run]

example [TransOrd α] (a : α) (b : β) : (mkDTreeMapSingleton a b).contains a := by
  simp [mkDTreeMapSingleton, Id.run]

example [TransOrd α] (a : α) : (mkTreeSetSingleton a).contains a := by
  simp [mkTreeSetSingleton, Id.run]

namespace DTreeMap.Raw

def t : DTreeMap.Raw Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: [⟨2, 8⟩] -/
#guard_msgs in
#eval (t.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨1, none⟩, ⟨2, some 8⟩, ⟨3, none⟩] -/
#guard_msgs in
#eval (t.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨3, 6⟩] -/
#guard_msgs in
#eval (t.filter fun _ v => v > 4).toList

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for ⟨k, v⟩ in t do
    ans := (k, v) :: ans
  return ans

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.toList

/-- info: #[⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.toArray

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DTreeMap.Raw.Const.toList t

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DTreeMap.Raw.Const.toArray t

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval t.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval t.keysArray

/-- info: [2, 4, 6] -/
#guard_msgs in
#eval t.values

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval (DTreeMap.Raw.Const.ofList [(1, 2), (2, 4), (3, 6)]).toList

/-- info: Std.DTreeMap.Raw.ofList [⟨1, 4⟩] -/
#guard_msgs in
#eval DTreeMap.Raw.Const.ofList [(1, 2), (1, 4)]

local instance : Inhabited ((_ : Nat) × Nat) where
  default := ⟨0, 0⟩

/-- info: some ⟨2, 4⟩ -/
#guard_msgs in
#eval t.entryAtIdx? 1

/-- info: some (2, 4) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.entryAtIdx? t 1

/-- info: none -/
#guard_msgs in
#eval t.entryAtIdx? 3

/-- info: none -/
#guard_msgs in
#eval DTreeMap.Raw.Const.entryAtIdx? t 3

/-- info: ⟨2, 4⟩ -/
#guard_msgs in
#eval t.entryAtIdx! 1

/-- info: (2, 4) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.entryAtIdx! t 1

/-- info: ⟨2, 4⟩ -/
#guard_msgs in
#eval t.entryAtIdxD 1 ⟨42, 3⟩

/-- info: (2, 4) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.entryAtIdxD t 1 ⟨42, 3⟩

/-- info: ⟨42, 3⟩ -/
#guard_msgs in
#eval t.entryAtIdxD 3 ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.entryAtIdxD t 3 ⟨42, 3⟩

-- TODO: keyAtIdx

/-- info: some 2 -/
#guard_msgs in
#eval t.keyAtIdx? 1

/-- info: none -/
#guard_msgs in
#eval t.keyAtIdx? 3

/-- info: 2 -/
#guard_msgs in
#eval t.keyAtIdx! 1

/-- info: 2 -/
#guard_msgs in
#eval t.keyAtIdxD 1 42

/-- info: 42 -/
#guard_msgs in
#eval t.keyAtIdxD 3 42

/-- info: [none, none, some ⟨1, 2⟩, some ⟨2, 4⟩, some ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLT? x

/-- info: [none, none, some (1, 2), some (2, 4), some (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryLT? t x

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getEntryLT! x

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryLT! t x

/-- info: [⟨42, 3⟩, ⟨42, 3⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLTD x ⟨42, 3⟩

/-- info: [(42, 3), (42, 3), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryLTD t x (42, 3)

/-- info: [none, some ⟨1, 2⟩, some ⟨2, 4⟩, some ⟨3, 6⟩, some ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLE? x

/-- info: [none, some (1, 2), some (2, 4), some (3, 6), some (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryLE? t x

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getEntryLE! x

/-- info: [(1, 2), (2, 4), (3, 6), (3, 6)] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryLE! t x

/-- info: [⟨42, 3⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLED x ⟨42, 3⟩

/-- info: [(42, 3), (1, 2), (2, 4), (3, 6), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryLED t x ⟨42, 3⟩

/-- info: [some ⟨1, 2⟩, some ⟨1, 2⟩, some ⟨2, 4⟩, some ⟨3, 6⟩, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGE? x

/-- info: [some (1, 2), some (1, 2), some (2, 4), some (3, 6), none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryGE? t x

/-- info: [⟨1, 2⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getEntryGE! x

/-- info: [(1, 2), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => DTreeMap.Raw.Const.getEntryGE! t x

/-- info: [⟨1, 2⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩, ⟨42, 3⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGED x ⟨42, 3⟩

/-- info: [(1, 2), (1, 2), (2, 4), (3, 6), (42, 3)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryGED t x ⟨42, 3⟩

/-- info: [some ⟨1, 2⟩, some ⟨2, 4⟩, some ⟨3, 6⟩, none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGT? x

/-- info: [some (1, 2), some (2, 4), some (3, 6), none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryGT? t x

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getEntryGT! x

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => DTreeMap.Raw.Const.getEntryGT! t x

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩, ⟨42, 3⟩, ⟨42, 3⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGTD x ⟨42, 3⟩

/-- info: [(1, 2), (2, 4), (3, 6), (42, 3), (42, 3)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Raw.Const.getEntryGTD t x ⟨42, 3⟩

/-- info: [none, none, some 1, some 2, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getKeyLT! x

/-- info: [42, 42, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLTD x 42

/-- info: [none, some 1, some 2, some 3, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLE? x

/-- info: [1, 2, 3, 3] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getKeyLE! x

/-- info: [42, 1, 2, 3, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLED x 42

/-- info: [some 1, some 1, some 2, some 3, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGE? x

/-- info: [1, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getKeyGE! x

/-- info: [1, 1, 2, 3, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGED x 42

/-- info: [some 1, some 2, some 3, none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getKeyGT! x

/-- info: [1, 2, 3, 42, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGTD x 42

/-- info: some ⟨1, 2⟩ -/
#guard_msgs in
#eval t.minEntry?

/-- info: some (1, 2) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.minEntry? t

/-- info: none -/
#guard_msgs in
#eval (∅ : DTreeMap.Raw Nat fun _ => Nat).minEntry?

/-- info: none -/
#guard_msgs in
#eval DTreeMap.Raw.Const.minEntry? (∅ : DTreeMap.Raw Nat fun _ => Nat)

/-- info: ⟨1, 2⟩ -/
#guard_msgs in
#eval t.minEntry!

/-- info: (1, 2) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.minEntry! t

/-- info: ⟨1, 2⟩ -/
#guard_msgs in
#eval t.minEntryD ⟨42, 3⟩

/-- info: (1, 2) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.minEntryD t ⟨42, 3⟩

/-- info: ⟨42, 3⟩ -/
#guard_msgs in
#eval (∅ : DTreeMap.Raw Nat fun _ => Nat).minEntryD ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.minEntryD (∅ : DTreeMap.Raw Nat fun _ => Nat) ⟨42, 3⟩

/-- info: some ⟨3, 6⟩ -/
#guard_msgs in
#eval t.maxEntry?

/-- info: some (3, 6) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.maxEntry? t

/-- info: none -/
#guard_msgs in
#eval (∅ : DTreeMap.Raw Nat fun _ => Nat).maxEntry?

/-- info: none -/
#guard_msgs in
#eval DTreeMap.Raw.Const.maxEntry? (∅ : DTreeMap.Raw Nat fun _ => Nat)

/-- info: ⟨3, 6⟩ -/
#guard_msgs in
#eval t.maxEntry!

/-- info: (3, 6) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.maxEntry! t

/-- info: ⟨3, 6⟩ -/
#guard_msgs in
#eval t.maxEntryD ⟨42, 3⟩

/-- info: (3, 6) -/
#guard_msgs in
#eval DTreeMap.Raw.Const.maxEntryD t ⟨42, 3⟩

/-- info: ⟨42, 3⟩ -/
#guard_msgs in
#eval (∅ : DTreeMap.Raw Nat fun _ => Nat).maxEntryD ⟨42, 3⟩

/-- info: ⟨42, 3⟩ -/
#guard_msgs in
#eval DTreeMap.Raw.maxEntryD (∅ : DTreeMap.Raw Nat fun _ => Nat) ⟨42, 3⟩

/-- info: (Std.DTreeMap.Raw.ofList [⟨3, 6⟩], Std.DTreeMap.Raw.ofList [⟨1, 2⟩, ⟨2, 4⟩]) -/
#guard_msgs in
#eval t.partition fun k v => k + 3 == v

/-- info: (Std.DTreeMap.Raw.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩], Std.DTreeMap.Raw.ofList []) -/
#guard_msgs in
#eval t.partition fun _ _ => true

/-- info: (Std.DTreeMap.Raw.ofList [], Std.DTreeMap.Raw.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]) -/
#guard_msgs in
#eval t.partition fun _ _ => false

/-- info: (Std.DTreeMap.Raw.ofList [], Std.DTreeMap.Raw.ofList []) -/
#guard_msgs in
#eval (∅ : DTreeMap.Raw Nat fun _ => Nat).partition fun k v => k + 3 == v

/-- info: false -/
#guard_msgs in
#eval t.any fun _ _ => false

/-- info: true -/
#guard_msgs in
#eval t.any fun _ _ => true

/-- info: true -/
#guard_msgs in
#eval t.any fun k v => k + 3 == v

/-- info: false -/
#guard_msgs in
#eval t.any fun k v => k + 5 == v

/-- info: false -/
#guard_msgs in
#eval t.all fun _ _ => false

/-- info: true -/
#guard_msgs in
#eval t.all fun _ _ => true

/-- info: true -/
#guard_msgs in
#eval t.all fun k v => k + k == v

/-- info: false -/
#guard_msgs in
#eval t.all fun k v => k + 3 == v

/-- info: Std.DTreeMap.Raw.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.eraseMany []

/-- info: Std.DTreeMap.Raw.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.eraseMany [0]

/-- info: Std.DTreeMap.Raw.ofList [⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.eraseMany [1]

/-- info: Std.DTreeMap.Raw.ofList [] -/
#guard_msgs in
#eval t.eraseMany [1, 2, 3]

-- We can't prove the non-Const variant yet because Nat doesn't have a LawfulEqOrd instance
/-- info: Std.DTreeMap.Raw.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval DTreeMap.Raw.Const.mergeWith (fun _ v _ => v) t ∅

/-- info: Std.DTreeMap.Raw.ofList [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval DTreeMap.Raw.Const.mergeWith (fun _ v v' => v' - v) t (.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩])

end DTreeMap.Raw

namespace DTreeMap

def t : DTreeMap Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: [⟨2, 8⟩] -/
#guard_msgs in
#eval (t.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨1, none⟩, ⟨2, some 8⟩, ⟨3, none⟩] -/
#guard_msgs in
#eval (t.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨3, 6⟩] -/
#guard_msgs in
#eval (t.filter fun _ v => v > 4).toList

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for ⟨k, v⟩ in t do
    ans := (k, v) :: ans
  return ans

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.toList

/-- info: #[⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.toArray

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DTreeMap.Const.toList t

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DTreeMap.Const.toArray t

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval t.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval t.keysArray

/-- info: [2, 4, 6] -/
#guard_msgs in
#eval t.values

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval (DTreeMap.Const.ofList [(1, 2), (2, 4), (3, 6)]).toList

/-- info: Std.DTreeMap.ofList [⟨1, 4⟩] -/
#guard_msgs in
#eval DTreeMap.Const.ofList [(1, 2), (1, 4)]

local instance : Inhabited ((_ : Nat) × Nat) where
  default := ⟨0, 0⟩

/-- info: some ⟨2, 4⟩ -/
#guard_msgs in
#eval t.entryAtIdx? 1

/-- info: some (2, 4) -/
#guard_msgs in
#eval DTreeMap.Const.entryAtIdx? t 1

/--
info: ⟨2, 4⟩
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! t.entryAtIdx 1 sorry

/--
info: (2, 4)
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! DTreeMap.Const.entryAtIdx t 1 sorry

/-- info: none -/
#guard_msgs in
#eval t.entryAtIdx? 3

/-- info: none -/
#guard_msgs in
#eval DTreeMap.Const.entryAtIdx? t 3

/-- info: ⟨2, 4⟩ -/
#guard_msgs in
#eval t.entryAtIdx! 1

/-- info: (2, 4) -/
#guard_msgs in
#eval DTreeMap.Const.entryAtIdx! t 1

/-- info: ⟨2, 4⟩ -/
#guard_msgs in
#eval t.entryAtIdxD 1 ⟨42, 3⟩

/-- info: (2, 4) -/
#guard_msgs in
#eval DTreeMap.Const.entryAtIdxD t 1 ⟨42, 3⟩

/-- info: ⟨42, 3⟩ -/
#guard_msgs in
#eval t.entryAtIdxD 3 ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval DTreeMap.Const.entryAtIdxD t 3 ⟨42, 3⟩

/-- info: some 2 -/
#guard_msgs in
#eval t.keyAtIdx? 1

/-- info: none -/
#guard_msgs in
#eval t.keyAtIdx? 3

/--
info: 2
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! t.keyAtIdx 1 sorry

/-- info: 2 -/
#guard_msgs in
#eval t.keyAtIdx! 1

/-- info: 2 -/
#guard_msgs in
#eval t.keyAtIdxD 1 42

/-- info: 42 -/
#guard_msgs in
#eval t.keyAtIdxD 3 42

/-- info: [none, none, some ⟨1, 2⟩, some ⟨2, 4⟩, some ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLT? x

/-- info: [none, none, some (1, 2), some (2, 4), some (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Const.getEntryLT? t x

/-
Cannot test `getEntryLT` etc. as of writing (2025-03-25) because
`TransOrd Nat` is not implemented yet.
-/

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getEntryLT! x

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => DTreeMap.Const.getEntryLT! t x

/-- info: [⟨42, 3⟩, ⟨42, 3⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLTD x ⟨42, 3⟩

/-- info: [(42, 3), (42, 3), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Const.getEntryLTD t x (42, 3)

/-- info: [none, some ⟨1, 2⟩, some ⟨2, 4⟩, some ⟨3, 6⟩, some ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLE? x

/-- info: [none, some (1, 2), some (2, 4), some (3, 6), some (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Const.getEntryLE? t x

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getEntryLE! x

/-- info: [(1, 2), (2, 4), (3, 6), (3, 6)] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => DTreeMap.Const.getEntryLE! t x

/-- info: [⟨42, 3⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLED x ⟨42, 3⟩

/-- info: [(42, 3), (1, 2), (2, 4), (3, 6), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Const.getEntryLED t x ⟨42, 3⟩

/-- info: [some ⟨1, 2⟩, some ⟨1, 2⟩, some ⟨2, 4⟩, some ⟨3, 6⟩, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGE? x

/-- info: [some (1, 2), some (1, 2), some (2, 4), some (3, 6), none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Const.getEntryGE? t x

/-- info: [⟨1, 2⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getEntryGE! x

/-- info: [(1, 2), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => DTreeMap.Const.getEntryGE! t x

/-- info: [⟨1, 2⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩, ⟨42, 3⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGED x ⟨42, 3⟩

/-- info: [(1, 2), (1, 2), (2, 4), (3, 6), (42, 3)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Const.getEntryGED t x ⟨42, 3⟩

/-- info: [some ⟨1, 2⟩, some ⟨2, 4⟩, some ⟨3, 6⟩, none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGT? x

/-- info: [some (1, 2), some (2, 4), some (3, 6), none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Const.getEntryGT? t x

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getEntryGT! x

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => DTreeMap.Const.getEntryGT! t x

/-- info: [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩, ⟨42, 3⟩, ⟨42, 3⟩] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGTD x ⟨42, 3⟩

/-- info: [(1, 2), (2, 4), (3, 6), (42, 3), (42, 3)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => DTreeMap.Const.getEntryGTD t x ⟨42, 3⟩

/-- info: [none, none, some 1, some 2, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getKeyLT! x

/-- info: [42, 42, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLTD x 42

/-- info: [none, some 1, some 2, some 3, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLE? x

/-- info: [1, 2, 3, 3] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getKeyLE! x

/-- info: [42, 1, 2, 3, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLED x 42

/-- info: [some 1, some 1, some 2, some 3, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGE? x

/-- info: [1, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getKeyGE! x

/-- info: [1, 1, 2, 3, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGED x 42

/-- info: [some 1, some 2, some 3, none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getKeyGT! x

/-- info: [1, 2, 3, 42, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGTD x 42

/-- info: some ⟨1, 2⟩ -/
#guard_msgs in
#eval t.minEntry?

/-- info: some (1, 2) -/
#guard_msgs in
#eval DTreeMap.Const.minEntry? t

/--
info: ⟨1, 2⟩
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! t.minEntry sorry

/--
info: (1, 2)
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! DTreeMap.Const.minEntry t sorry

/-- info: none -/
#guard_msgs in
#eval (∅ : DTreeMap.Raw Nat fun _ => Nat).minEntry?

/-- info: none -/
#guard_msgs in
#eval DTreeMap.Const.minEntry? (∅ : DTreeMap Nat fun _ => Nat)

/-- info: ⟨1, 2⟩ -/
#guard_msgs in
#eval t.minEntry!

/-- info: (1, 2) -/
#guard_msgs in
#eval DTreeMap.Const.minEntry! t

/-- info: ⟨1, 2⟩ -/
#guard_msgs in
#eval t.minEntryD ⟨42, 3⟩

/-- info: (1, 2) -/
#guard_msgs in
#eval DTreeMap.Const.minEntryD t ⟨42, 3⟩

/-- info: ⟨42, 3⟩ -/
#guard_msgs in
#eval (∅ : DTreeMap.Raw Nat fun _ => Nat).minEntryD ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval DTreeMap.Const.minEntryD (∅ : DTreeMap Nat fun _ => Nat) ⟨42, 3⟩

/-- info: some ⟨3, 6⟩ -/
#guard_msgs in
#eval t.maxEntry?

/-- info: some (3, 6) -/
#guard_msgs in
#eval DTreeMap.Const.maxEntry? t

/--
info: ⟨3, 6⟩
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! t.maxEntry sorry

/--
info: (3, 6)
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! DTreeMap.Const.maxEntry t sorry

/-- info: none -/
#guard_msgs in
#eval (∅ : DTreeMap Nat fun _ => Nat).maxEntry?

/-- info: none -/
#guard_msgs in
#eval DTreeMap.Const.maxEntry? (∅ : DTreeMap Nat fun _ => Nat)

/-- info: ⟨3, 6⟩ -/
#guard_msgs in
#eval t.maxEntry!

/-- info: (3, 6) -/
#guard_msgs in
#eval DTreeMap.Const.maxEntry! t

/-- info: ⟨3, 6⟩ -/
#guard_msgs in
#eval t.maxEntryD ⟨42, 3⟩

/-- info: (3, 6) -/
#guard_msgs in
#eval DTreeMap.Const.maxEntryD t ⟨42, 3⟩

/-- info: ⟨42, 3⟩ -/
#guard_msgs in
#eval (∅ : DTreeMap.Raw Nat fun _ => Nat).maxEntryD ⟨42, 3⟩

/-- info: ⟨42, 3⟩ -/
#guard_msgs in
#eval DTreeMap.maxEntryD (∅ : DTreeMap Nat fun _ => Nat) ⟨42, 3⟩

/-- info: (Std.DTreeMap.ofList [⟨3, 6⟩], Std.DTreeMap.ofList [⟨1, 2⟩, ⟨2, 4⟩]) -/
#guard_msgs in
#eval t.partition fun k v => k + 3 == v

/-- info: (Std.DTreeMap.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩], Std.DTreeMap.ofList []) -/
#guard_msgs in
#eval t.partition fun _ _ => true

/-- info: (Std.DTreeMap.ofList [], Std.DTreeMap.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]) -/
#guard_msgs in
#eval t.partition fun _ _ => false

/-- info: (Std.DTreeMap.ofList [], Std.DTreeMap.ofList []) -/
#guard_msgs in
#eval (∅ : DTreeMap Nat fun _ => Nat).partition fun k v => k + 3 == v

/-- info: false -/
#guard_msgs in
#eval t.any fun _ _ => false

/-- info: true -/
#guard_msgs in
#eval t.any fun _ _ => true

/-- info: true -/
#guard_msgs in
#eval t.any fun k v => k + 3 == v

/-- info: false -/
#guard_msgs in
#eval t.any fun k v => k + 5 == v

/-- info: false -/
#guard_msgs in
#eval t.all fun _ _ => false

/-- info: true -/
#guard_msgs in
#eval t.all fun _ _ => true

/-- info: true -/
#guard_msgs in
#eval t.all fun k v => k + k == v

/-- info: false -/
#guard_msgs in
#eval t.all fun k v => k + 3 == v

/-- info: Std.DTreeMap.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.eraseMany []

/-- info: Std.DTreeMap.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.eraseMany [0]

/-- info: Std.DTreeMap.ofList [⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval t.eraseMany [1]

/-- info: Std.DTreeMap.ofList [] -/
#guard_msgs in
#eval t.eraseMany [1, 2, 3]

-- We can't prove the non-Const variant yet because Nat doesn't have a LawfulEqOrd instance
/-- info: Std.DTreeMap.ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval DTreeMap.Const.mergeWith (fun _ v _ => v) t ∅

/-- info: Std.DTreeMap.ofList [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval DTreeMap.Const.mergeWith (fun _ v v' => v' - v) t (.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩])

end DTreeMap

namespace TreeMap.Raw

def t : TreeMap.Raw Nat Nat :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: [(2, 8)] -/
#guard_msgs in
#eval (t.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(1, none), (2, some 8), (3, none)] -/
#guard_msgs in
#eval (t.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(3, 6)] -/
#guard_msgs in
#eval (t.filter fun _ v => v > 4).toList

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for ⟨k, v⟩ in t do
    ans := (k, v) :: ans
  return ans

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval t.toList

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval t.toArray

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval t.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval t.keysArray

/-- info: [2, 4, 6] -/
#guard_msgs in
#eval t.values

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval (TreeMap.Raw.ofList [(1, 2), (2, 4), (3, 6)]).toList

/-- info: Std.TreeMap.Raw.ofList [(1, 4)] -/
#guard_msgs in
#eval TreeMap.Raw.ofList [(1, 2), (1, 4)]

local instance : Inhabited ((_ : Nat) × Nat) where
  default := ⟨0, 0⟩

/-- info: some (2, 4) -/
#guard_msgs in
#eval t.entryAtIdx? 1

/-- info: none -/
#guard_msgs in
#eval t.entryAtIdx? 3

/-- info: (2, 4) -/
#guard_msgs in
#eval t.entryAtIdx! 1

/-- info: (2, 4) -/
#guard_msgs in
#eval t.entryAtIdxD 1 ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval t.entryAtIdxD 3 ⟨42, 3⟩

/-- info: some 2 -/
#guard_msgs in
#eval t.keyAtIdx? 1

/-- info: none -/
#guard_msgs in
#eval t.keyAtIdx? 3

/-- info: 2 -/
#guard_msgs in
#eval t.keyAtIdx! 1

/-- info: 2 -/
#guard_msgs in
#eval t.keyAtIdxD 1 42

/-- info: 42 -/
#guard_msgs in
#eval t.keyAtIdxD 3 42

/-- info: [none, none, some (1, 2), some (2, 4), some (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLT? x

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getEntryLT! x

/-- info: [(42, 3), (42, 3), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLTD x ⟨42, 3⟩

/-- info: [none, some (1, 2), some (2, 4), some (3, 6), some (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLE? x

/-- info: [(1, 2), (2, 4), (3, 6), (3, 6)] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getEntryLE! x

/-- info: [(42, 3), (1, 2), (2, 4), (3, 6), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLED x ⟨42, 3⟩

/-- info: [some (1, 2), some (1, 2), some (2, 4), some (3, 6), none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGE? x

/-- info: [(1, 2), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getEntryGE! x

/-- info: [(1, 2), (1, 2), (2, 4), (3, 6), (42, 3)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGED x ⟨42, 3⟩

/-- info: [some (1, 2), some (2, 4), some (3, 6), none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGT? x

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getEntryGT! x

/-- info: [(1, 2), (2, 4), (3, 6), (42, 3), (42, 3)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGTD x ⟨42, 3⟩

/-- info: [none, none, some 1, some 2, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getKeyLT! x

/-- info: [42, 42, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLTD x 42

/-- info: [none, some 1, some 2, some 3, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLE? x

/-- info: [1, 2, 3, 3] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getKeyLE! x

/-- info: [42, 1, 2, 3, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLED x 42

/-- info: [some 1, some 1, some 2, some 3, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGE? x

/-- info: [1, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getKeyGE! x

/-- info: [1, 1, 2, 3, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGED x 42

/-- info: [some 1, some 2, some 3, none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getKeyGT! x

/-- info: [1, 2, 3, 42, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGTD x 42

/-- info: some (1, 2) -/
#guard_msgs in
#eval t.minEntry?

/-- info: none -/
#guard_msgs in
#eval (∅ : TreeMap.Raw Nat Nat).minEntry?

/-- info: (1, 2) -/
#guard_msgs in
#eval t.minEntry!

/-- info: (1, 2) -/
#guard_msgs in
#eval t.minEntryD ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval (∅ : TreeMap.Raw Nat Nat).minEntryD ⟨42, 3⟩

/-- info: some (3, 6) -/
#guard_msgs in
#eval t.maxEntry?

/-- info: none -/
#guard_msgs in
#eval (∅ : TreeMap.Raw Nat Nat).maxEntry?

/-- info: (3, 6) -/
#guard_msgs in
#eval t.maxEntry!

/-- info: (3, 6) -/
#guard_msgs in
#eval t.maxEntryD ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval (∅ : TreeMap.Raw Nat Nat).maxEntryD ⟨42, 3⟩

/-- info: (Std.TreeMap.Raw.ofList [(3, 6)], Std.TreeMap.Raw.ofList [(1, 2), (2, 4)]) -/
#guard_msgs in
#eval t.partition fun k v => k + 3 == v

/-- info: (Std.TreeMap.Raw.ofList [(1, 2), (2, 4), (3, 6)], Std.TreeMap.Raw.ofList []) -/
#guard_msgs in
#eval t.partition fun _ _ => true

/-- info: (Std.TreeMap.Raw.ofList [], Std.TreeMap.Raw.ofList [(1, 2), (2, 4), (3, 6)]) -/
#guard_msgs in
#eval t.partition fun _ _ => false

/-- info: (Std.TreeMap.Raw.ofList [], Std.TreeMap.Raw.ofList []) -/
#guard_msgs in
#eval (∅ : TreeMap.Raw Nat Nat).partition fun k v => k + 3 == v

/-- info: false -/
#guard_msgs in
#eval t.any fun _ _ => false

/-- info: true -/
#guard_msgs in
#eval t.any fun _ _ => true

/-- info: true -/
#guard_msgs in
#eval t.any fun k v => k + 3 == v

/-- info: false -/
#guard_msgs in
#eval t.any fun k v => k + 5 == v

/-- info: false -/
#guard_msgs in
#eval t.all fun _ _ => false

/-- info: true -/
#guard_msgs in
#eval t.all fun _ _ => true

/-- info: true -/
#guard_msgs in
#eval t.all fun k v => k + k == v

/-- info: false -/
#guard_msgs in
#eval t.all fun k v => k + 3 == v

/-- info: Std.TreeMap.Raw.ofList [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval t.eraseMany []

/-- info: Std.TreeMap.Raw.ofList [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval t.eraseMany [0]

/-- info: Std.TreeMap.Raw.ofList [(2, 4), (3, 6)] -/
#guard_msgs in
#eval t.eraseMany [1]

/-- info: Std.TreeMap.Raw.ofList [] -/
#guard_msgs in
#eval t.eraseMany [1, 2, 3]

/-- info: Std.TreeMap.Raw.ofList [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval TreeMap.Raw.mergeWith (fun _ v _ => v) t ∅

/-- info: Std.TreeMap.Raw.ofList [(0, 0), (1, 0), (2, 0), (3, 6)] -/
#guard_msgs in
#eval TreeMap.Raw.mergeWith (fun _ v v' => v' - v) t (.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩])

end TreeMap.Raw

namespace TreeMap

def t : TreeMap Nat Nat :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: [(2, 8)] -/
#guard_msgs in
#eval (t.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(1, none), (2, some 8), (3, none)] -/
#guard_msgs in
#eval (t.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(3, 6)] -/
#guard_msgs in
#eval (t.filter fun _ v => v > 4).toList

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for ⟨k, v⟩ in t do
    ans := (k, v) :: ans
  return ans

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval t.toList

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval t.toArray

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval t.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval t.keysArray

/-- info: [2, 4, 6] -/
#guard_msgs in
#eval t.values

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval (TreeMap.ofList [(1, 2), (2, 4), (3, 6)]).toList

/-- info: Std.TreeMap.ofList [(1, 4)] -/
#guard_msgs in
#eval TreeMap.ofList [(1, 2), (1, 4)]

local instance : Inhabited ((_ : Nat) × Nat) where
  default := ⟨0, 0⟩

/-- info: some (2, 4) -/
#guard_msgs in
#eval t.entryAtIdx? 1

/-- info: none -/
#guard_msgs in
#eval t.entryAtIdx? 3

/--
info: (2, 4)
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! t.entryAtIdx 1 sorry

/-- info: (2, 4) -/
#guard_msgs in
#eval t.entryAtIdx! 1

/-- info: (2, 4) -/
#guard_msgs in
#eval t.entryAtIdxD 1 ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval t.entryAtIdxD 3 ⟨42, 3⟩

/-- info: some 2 -/
#guard_msgs in
#eval t.keyAtIdx? 1

/-- info: none -/
#guard_msgs in
#eval t.keyAtIdx? 3

/--
info: 2
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! t.keyAtIdx 1 sorry

/-- info: 2 -/
#guard_msgs in
#eval t.keyAtIdx! 1

/-- info: 2 -/
#guard_msgs in
#eval t.keyAtIdxD 1 42

/-- info: 42 -/
#guard_msgs in
#eval t.keyAtIdxD 3 42

/-- info: [none, none, some (1, 2), some (2, 4), some (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLT? x

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getEntryLT! x

/-- info: [(42, 3), (42, 3), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLTD x ⟨42, 3⟩

/-- info: [none, some (1, 2), some (2, 4), some (3, 6), some (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLE? x

/-- info: [(1, 2), (2, 4), (3, 6), (3, 6)] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getEntryLE! x

/-- info: [(42, 3), (1, 2), (2, 4), (3, 6), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryLED x ⟨42, 3⟩

/-- info: [some (1, 2), some (1, 2), some (2, 4), some (3, 6), none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGE? x

/-- info: [(1, 2), (1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getEntryGE! x

/-- info: [(1, 2), (1, 2), (2, 4), (3, 6), (42, 3)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGED x ⟨42, 3⟩

/-- info: [some (1, 2), some (2, 4), some (3, 6), none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGT? x

/-- info: [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getEntryGT! x

/-- info: [(1, 2), (2, 4), (3, 6), (42, 3), (42, 3)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getEntryGTD x ⟨42, 3⟩

/-- info: [none, none, some 1, some 2, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getKeyLT! x

/-- info: [42, 42, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLTD x 42

/-- info: [none, some 1, some 2, some 3, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLE? x

/-- info: [1, 2, 3, 3] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getKeyLE! x

/-- info: [42, 1, 2, 3, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyLED x 42

/-- info: [some 1, some 1, some 2, some 3, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGE? x

/-- info: [1, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getKeyGE! x

/-- info: [1, 1, 2, 3, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGED x 42

/-- info: [some 1, some 2, some 3, none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getKeyGT! x

/-- info: [1, 2, 3, 42, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getKeyGTD x 42

/-- info: some (1, 2) -/
#guard_msgs in
#eval t.minEntry?

/--
info: (1, 2)
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! t.minEntry sorry

/-- info: none -/
#guard_msgs in
#eval (∅ : TreeMap Nat Nat).minEntry?

/-- info: (1, 2) -/
#guard_msgs in
#eval t.minEntry!

/-- info: (1, 2) -/
#guard_msgs in
#eval t.minEntryD ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval (∅ : TreeMap Nat Nat).minEntryD ⟨42, 3⟩

/-- info: some (3, 6) -/
#guard_msgs in
#eval t.maxEntry?

/-- info: none -/
#guard_msgs in
#eval (∅ : TreeMap Nat Nat).maxEntry?

/--
info: (3, 6)
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! t.maxEntry sorry

/-- info: (3, 6) -/
#guard_msgs in
#eval t.maxEntry!

/-- info: (3, 6) -/
#guard_msgs in
#eval t.maxEntryD ⟨42, 3⟩

/-- info: (42, 3) -/
#guard_msgs in
#eval (∅ : TreeMap Nat Nat).maxEntryD ⟨42, 3⟩

/-- info: (Std.TreeMap.ofList [(3, 6)], Std.TreeMap.ofList [(1, 2), (2, 4)]) -/
#guard_msgs in
#eval t.partition fun k v => k + 3 == v

/-- info: (Std.TreeMap.ofList [(1, 2), (2, 4), (3, 6)], Std.TreeMap.ofList []) -/
#guard_msgs in
#eval t.partition fun _ _ => true

/-- info: (Std.TreeMap.ofList [], Std.TreeMap.ofList [(1, 2), (2, 4), (3, 6)]) -/
#guard_msgs in
#eval t.partition fun _ _ => false

/-- info: (Std.TreeMap.ofList [], Std.TreeMap.ofList []) -/
#guard_msgs in
#eval (∅ : TreeMap Nat Nat).partition fun k v => k + 3 == v

/-- info: false -/
#guard_msgs in
#eval t.any fun _ _ => false

/-- info: true -/
#guard_msgs in
#eval t.any fun _ _ => true

/-- info: true -/
#guard_msgs in
#eval t.any fun k v => k + 3 == v

/-- info: false -/
#guard_msgs in
#eval t.any fun k v => k + 5 == v

/-- info: false -/
#guard_msgs in
#eval t.all fun _ _ => false

/-- info: true -/
#guard_msgs in
#eval t.all fun _ _ => true

/-- info: true -/
#guard_msgs in
#eval t.all fun k v => k + k == v

/-- info: false -/
#guard_msgs in
#eval t.all fun k v => k + 3 == v

/-- info: Std.TreeMap.ofList [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval t.eraseMany []

/-- info: Std.TreeMap.ofList [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval t.eraseMany [0]

/-- info: Std.TreeMap.ofList [(2, 4), (3, 6)] -/
#guard_msgs in
#eval t.eraseMany [1]

/-- info: Std.TreeMap.ofList [] -/
#guard_msgs in
#eval t.eraseMany [1, 2, 3]

/-- info: Std.TreeMap.ofList [(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval TreeMap.mergeWith (fun _ v _ => v) t ∅

/-- info: Std.TreeMap.ofList [(0, 0), (1, 0), (2, 0), (3, 6)] -/
#guard_msgs in
#eval TreeMap.mergeWith (fun _ v v' => v' - v) t (.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩])

end TreeMap

namespace TreeSet.Raw

def t : TreeSet.Raw Nat :=
  .ofList [1, 2, 3]

/-- info: [3] -/
#guard_msgs in
#eval (t.filter fun k => k > 2).toList

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval t.toList

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval t.toArray

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval (TreeSet.Raw.ofList [1, 2, 3]).toList

/-- info: Std.TreeSet.Raw.ofList [1] -/
#guard_msgs in
#eval TreeSet.Raw.ofList [1, 1]

/-- info: some 2 -/
#guard_msgs in
#eval t.atIdx? 1

/-- info: none -/
#guard_msgs in
#eval t.atIdx? 3

/-- info: 2 -/
#guard_msgs in
#eval t.atIdx! 1

/-- info: 2 -/
#guard_msgs in
#eval t.atIdxD 1 42

/-- info: 42 -/
#guard_msgs in
#eval t.atIdxD 3 42

/-- info: [none, none, some 1, some 2, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getLT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getLT! x

/-- info: [42, 42, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getLTD x 42

/-- info: [none, some 1, some 2, some 3, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getLE? x

/-- info: [1, 2, 3, 3] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getLE! x

/-- info: [42, 1, 2, 3, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getLED x 42

/-- info: [some 1, some 1, some 2, some 3, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getGE? x

/-- info: [1, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getGE! x

/-- info: [1, 1, 2, 3, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getGED x 42

/-- info: [some 1, some 2, some 3, none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getGT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getGT! x

/-- info: [1, 2, 3, 42, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getGTD x 42

/-- info: (Std.TreeSet.Raw.ofList [3], Std.TreeSet.Raw.ofList [1, 2]) -/
#guard_msgs in
#eval t.partition fun k => k == 3

/-- info: (Std.TreeSet.Raw.ofList [1, 2, 3], Std.TreeSet.Raw.ofList []) -/
#guard_msgs in
#eval t.partition fun _ => true

/-- info: (Std.TreeSet.Raw.ofList [], Std.TreeSet.Raw.ofList [1, 2, 3]) -/
#guard_msgs in
#eval t.partition fun _ => false

/-- info: (Std.TreeSet.Raw.ofList [], Std.TreeSet.Raw.ofList []) -/
#guard_msgs in
#eval (∅ : TreeSet.Raw Nat).partition fun k => k == 3

/-- info: false -/
#guard_msgs in
#eval t.any fun _ => false

/-- info: true -/
#guard_msgs in
#eval t.any fun _ => true

/-- info: true -/
#guard_msgs in
#eval t.any fun k => k == 3

/-- info: false -/
#guard_msgs in
#eval t.any fun k => k == 5

/-- info: false -/
#guard_msgs in
#eval t.all fun _ => false

/-- info: true -/
#guard_msgs in
#eval t.all fun _ => true

/-- info: true -/
#guard_msgs in
#eval t.all fun k => k < 6

/-- info: false -/
#guard_msgs in
#eval t.all fun k => k == 3

/-- info: Std.TreeSet.Raw.ofList [1, 2, 3] -/
#guard_msgs in
#eval t.eraseMany []

/-- info: Std.TreeSet.Raw.ofList [1, 2, 3] -/
#guard_msgs in
#eval t.eraseMany [0]

/-- info: Std.TreeSet.Raw.ofList [2, 3] -/
#guard_msgs in
#eval t.eraseMany [1]

/-- info: Std.TreeSet.Raw.ofList [] -/
#guard_msgs in
#eval t.eraseMany [1, 2, 3]

/-- info: Std.TreeSet.Raw.ofList [1, 2, 3] -/
#guard_msgs in
#eval TreeSet.Raw.merge t ∅

/-- info: Std.TreeSet.Raw.ofList [0, 1, 2, 3] -/
#guard_msgs in
#eval TreeSet.Raw.merge t (.ofList [0, 1, 2])

end TreeSet.Raw

namespace TreeSet

def t : TreeSet Nat :=
  .ofList [1, 2, 3]

/-- info: [3] -/
#guard_msgs in
#eval (t.filter fun k => k > 2).toList

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval t.toList

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval t.toArray

/-- info: some 2 -/
#guard_msgs in
#eval t.atIdx? 1

/-- info: none -/
#guard_msgs in
#eval t.atIdx? 3

/--
info: 2
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! t.atIdx 1 sorry

/-- info: 2 -/
#guard_msgs in
#eval t.atIdx! 1

/-- info: 2 -/
#guard_msgs in
#eval t.atIdxD 1 42

/-- info: 42 -/
#guard_msgs in
#eval t.atIdxD 3 42

/-- info: [none, none, some 1, some 2, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getLT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [2, 3, 4].map fun x => t.getLT! x

/-- info: [42, 42, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getLTD x 42

/-- info: [none, some 1, some 2, some 3, some 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getLE? x

/-- info: [1, 2, 3, 3] -/
#guard_msgs in
#eval [1, 2, 3, 4].map fun x => t.getLE! x

/-- info: [42, 1, 2, 3, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getLED x 42

/-- info: [some 1, some 1, some 2, some 3, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getGE? x

/-- info: [1, 1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2, 3].map fun x => t.getGE! x

/-- info: [1, 1, 2, 3, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getGED x 42

/-- info: [some 1, some 2, some 3, none, none] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getGT? x

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [0, 1, 2].map fun x => t.getGT! x

/-- info: [1, 2, 3, 42, 42] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map fun x => t.getGTD x 42

/-- info: (Std.TreeSet.ofList [3], Std.TreeSet.ofList [1, 2]) -/
#guard_msgs in
#eval t.partition fun k => k == 3

/-- info: (Std.TreeSet.ofList [1, 2, 3], Std.TreeSet.ofList []) -/
#guard_msgs in
#eval t.partition fun _ => true

/-- info: (Std.TreeSet.ofList [], Std.TreeSet.ofList [1, 2, 3]) -/
#guard_msgs in
#eval t.partition fun _ => false

/-- info: (Std.TreeSet.ofList [], Std.TreeSet.ofList []) -/
#guard_msgs in
#eval (∅ : TreeSet Nat).partition fun k => k == 3

/-- info: false -/
#guard_msgs in
#eval t.any fun _ => false

/-- info: true -/
#guard_msgs in
#eval t.any fun _ => true

/-- info: true -/
#guard_msgs in
#eval t.any fun k => k == 3

/-- info: false -/
#guard_msgs in
#eval t.any fun k => k == 5

/-- info: false -/
#guard_msgs in
#eval t.all fun _ => false

/-- info: true -/
#guard_msgs in
#eval t.all fun _ => true

/-- info: true -/
#guard_msgs in
#eval t.all fun k => k < 6

/-- info: false -/
#guard_msgs in
#eval t.all fun k => k == 3

/-- info: Std.TreeSet.ofList [1, 2, 3] -/
#guard_msgs in
#eval t.eraseMany []

/-- info: Std.TreeSet.ofList [1, 2, 3] -/
#guard_msgs in
#eval t.eraseMany [0]

/-- info: Std.TreeSet.ofList [2, 3] -/
#guard_msgs in
#eval t.eraseMany [1]

/-- info: Std.TreeSet.ofList [] -/
#guard_msgs in
#eval t.eraseMany [1, 2, 3]

/-- info: Std.TreeSet.ofList [1, 2, 3] -/
#guard_msgs in
#eval TreeSet.merge t ∅

/-- info: Std.TreeSet.ofList [0, 1, 2, 3] -/
#guard_msgs in
#eval TreeSet.merge t (.ofList [0, 1, 2])

end TreeSet
