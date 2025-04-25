import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.DHashMap

open Std (DHashMap HashMap HashSet)

/-! (Non-exhaustive) tests that `BEq` and `Hashable` arguments to query operations and lemmas are
correctly solved by unification. -/

namespace DHashMap

structure A (α) extends BEq α, Hashable α where
  foo : DHashMap α (fun _ => Nat)

def A.add (xs : A α) (x : α) : A α :=
  {xs with foo := xs.foo.insert x 5}

example (xs : A α) (x : α) : ¬x ∈ @DHashMap.emptyWithCapacity _ (fun _ => Nat) xs.toBEq xs.toHashable 5 :=
  DHashMap.not_mem_emptyWithCapacity

example (xs : A α) (x : α) : (@DHashMap.emptyWithCapacity _ (fun _ => Nat) xs.toBEq xs.toHashable 5).contains x = false := by
  rw [DHashMap.contains_emptyWithCapacity]

example (xs : A α) (x : α) : DHashMap.Const.get? (@DHashMap.emptyWithCapacity _ (fun _ => Nat) xs.toBEq xs.toHashable 5) x = none := by
  rw [DHashMap.Const.get?_emptyWithCapacity]

example (xs : A α) (x : α) [@LawfulBEq α xs.toBEq] : xs.foo.size ≤ (xs.foo.insert x 5).size :=
  DHashMap.size_le_size_insert

end DHashMap

namespace HashMap

structure A (α) extends BEq α, Hashable α where
  foo : HashMap α Nat

def A.add (xs : A α) (x : α) : A α :=
  {xs with foo := xs.foo.insert x 5}

example (xs : A α) (x : α) : ¬x ∈ @HashMap.emptyWithCapacity _ Nat xs.toBEq xs.toHashable 5 :=
  HashMap.not_mem_emptyWithCapacity

example (xs : A α) (x : α) : (@HashMap.emptyWithCapacity _ Nat xs.toBEq xs.toHashable 5).contains x = false := by
  rw [HashMap.contains_emptyWithCapacity]

example (xs : A α) (x : α) : (@HashMap.emptyWithCapacity _ Nat xs.toBEq xs.toHashable 5)[x]? = none := by
  rw [HashMap.getElem?_emptyWithCapacity]

example (xs : A α) (x : α) [@LawfulBEq α xs.toBEq] : xs.foo.size ≤ (xs.foo.insert x 5).size :=
  HashMap.size_le_size_insert

end HashMap

namespace HashSet

structure A (α) extends BEq α, Hashable α where
  foo : HashSet α

def A.add (xs : A α) (x : α) : A α :=
  {xs with foo := xs.foo.insert x}

example (xs : A α) (x : α) : ¬x ∈ @HashSet.emptyWithCapacity _ xs.toBEq xs.toHashable 5 :=
  HashSet.not_mem_emptyWithCapacity

example (xs : A α) (x : α) : (@HashSet.emptyWithCapacity _ xs.toBEq xs.toHashable 5).contains x = false := by
  rw [HashSet.contains_emptyWithCapacity]

example (xs : A α) (x : α) [@LawfulBEq α xs.toBEq] : xs.foo.size ≤ (xs.foo.insert x).size :=
  HashSet.size_le_size_insert

end HashSet
