import Std

open Std

example {cmp : α → α → Ordering} [TransCmp cmp] (m : ExtTreeSet α cmp) (x : α) :
    (m.insert x).erase x = m.erase x := by
  grind

example (m : ExtTreeSet Nat compare) (x : Nat) : (m.insert x).erase x = m.erase x := by
  grind

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (m : ExtHashSet α) (x : α) :
    (m.insert x).erase x = m.erase x := by
  grind

example (m : ExtHashMap Int Int) (x y : Int) : (m.insert x y).erase x = m.erase x := by
  grind
