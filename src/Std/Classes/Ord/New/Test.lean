import Std.Classes.Ord.New.PartiallyComparable
import Std.Data.TreeMap

open Std

example (α : Type u) [Ord α] [pc : PartiallyComparable α] [LawfulPartiallyComparableOrd pc]
    [LawfulLinearOrder pc] : Unit := Id.run do
  let mut m : DTreeMap α (fun _ => Nat) := ∅
  let x := m.get sorry sorry
  sorry
