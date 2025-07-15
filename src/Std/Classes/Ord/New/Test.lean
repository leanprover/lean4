import Std.Classes.Ord.New.PartiallyComparable
import Std.Data.TreeMap

open Std

def test {α : Type u} [Ord α] [LawfulPartiallyComparableOrd (.ofOrd α)]
    [LawfulLinearOrder (.ofOrd α)] (a : α) : Option Nat :=
  (∅ : DTreeMap α (fun _ => Nat)).get? a

example (α : Type u) [Ord α] [LawfulPartiallyComparableOrd (.ofOrd α)]
    [LawfulLinearOrder (.ofOrd α)] (a : α) :
    test a = none := by
  rw [test]
  rw [DTreeMap.get?_emptyc]
