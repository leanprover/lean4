/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Init.Data.List.Erase
import Init.Data.Array.Lemmas
import Std.Sat.CNF.Basic
import Std.Tactic.BVDecide.LRAT.Internal.PosFin
import Std.Tactic.BVDecide.LRAT.Internal.Assignment


namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

open Std.Sat

/--
An inductive datatype used specifically for the output of the `reduce` function. The intended
meaning of each constructor is explained in the docstring of the `reduce` function.
-/
inductive ReduceResult (α : Type u)
  | encounteredBoth
  | reducedToEmpty
  | reducedToUnit (l : Literal α)
  | reducedToNonunit

/--
Typeclass for clauses. An instance `[Clause α β]` indicates that `β` is the type of a clause with
variables of type `α`.
-/
class Clause (α : outParam (Type u)) (β : Type v) where
  toList : β → CNF.Clause α
  not_tautology : ∀ c : β, ∀ l : Literal α, l ∉ toList c ∨ Literal.negate l ∉ toList c
  /-- Returns none if the given array contains complementary literals -/
  ofArray : Array (Literal α) → Option β
  ofArray_eq :
    ∀ arr : Array (Literal α), (∀ i : Fin arr.size, ∀ j : Fin arr.size, i.1 ≠ j.1 → arr[i] ≠ arr[j]) →
      ∀ c : β, ofArray arr = some c → toList c = arr.toList
  empty : β
  empty_eq : toList empty = []
  unit : Literal α → β
  unit_eq : ∀ l : Literal α, toList (unit l) = [l]
  isUnit : β → Option (Literal α)
  isUnit_iff : ∀ c : β, ∀ l : Literal α, isUnit c = some l ↔ toList c = [l]
  negate : β → CNF.Clause α
  negate_eq : ∀ c : β, negate c = (toList c).map Literal.negate
  /-- Returns none if the result is a tautology. -/
  insert : β → Literal α → Option β
  delete : β → Literal α → β
  delete_iff : ∀ c : β, ∀ l : Literal α, ∀ l' : Literal α,
    l' ∈ toList (delete c l) ↔ l' ≠ l ∧ l' ∈ toList c
  contains : β → Literal α → Bool
  contains_iff : ∀ c : β, ∀ l : Literal α, contains c l ↔ l ∈ toList c
  /-- Reduces the clause with respect to the given assignment -/
  reduce : β → Array Assignment → ReduceResult α

namespace Clause

instance : Entails α (Literal α) where
  eval := fun p l => p l.1 = l.2

instance (p : α → Bool) (l : Literal α) : Decidable (p ⊨ l) :=
  inferInstanceAs (Decidable (p l.1 = l.2))

def eval [Clause α β] (a : α → Bool) (c : β) : Bool :=
  (toList c).any fun (l : Literal α) => a ⊨ l

instance [Clause α β] : Entails α β where
  eval a c := Clause.eval a c

instance [Clause α β] (p : α → Bool) (c : β) : Decidable (p ⊨ c) :=
  inferInstanceAs (Decidable (Clause.eval p c = true))

instance [Clause α β] : Inhabited β where
  default := empty

end Clause

/--
The `DefaultClause` structure is primarily a list of literals. The additional field `nodupkey` is
included to ensure that `not_tautology` is provable (which is needed to prove `sat_of_insertRup`
and `sat_of_insertRat` in `LRAT.Formula.Internal.RupAddSound` and `LRAT.Formula.Internal.RatAddSound`).
The additional field `nodup` is included to ensure that `delete` can be implemented by simply calling
`erase` on the `clause` field. Without `nodup`, it would be necessary to iterate through the entire
`clause` field and erase all instances of the literal to be deleted, since there would potentially
be more than one.

In principle, one could combine `nodupkey` and `nodup` to instead have one additional field that
stipulates that `∀ l1 : PosFin numVarsSucc, ∀ l2 : PosFin numVarsSucc, l1.1 ≠ l2.1`. This would work
just as well, and the only reason that `DefaultClause` is structured in this manner is that the
`nodup` field was only included in a later stage of the verification process when it became clear
that it was needed.
-/
@[ext] structure DefaultClause (numVarsSucc : Nat) where
  clause : CNF.Clause (PosFin numVarsSucc)
  nodupkey : ∀ l : PosFin numVarsSucc, (l, true) ∉ clause ∨ (l, false) ∉ clause
  nodup : List.Nodup clause
  deriving BEq

instance : ToString (DefaultClause n) where
  toString c := s!"{c.clause.reverse}"

namespace DefaultClause

def toList (c : DefaultClause n) : CNF.Clause (PosFin n) := c.clause

theorem not_tautology (c : DefaultClause n) (l : Literal (PosFin n)) :
    l ∉ toList c ∨ ¬Literal.negate l ∈ toList c := by
  simp only [toList, Literal.negate]
  have h := c.nodupkey l.1
  by_cases hl : l.2
  · simp only [hl, Bool.not_true]
    rwa [← hl] at h
  · simp only [Bool.not_eq_true] at hl
    simp only [hl, Bool.not_false]
    apply Or.symm
    rwa [← hl] at h

def empty : DefaultClause n :=
  let clause := []
  have nodupkey := by
    simp only [clause, List.find?, List.not_mem_nil, not_false_eq_true, or_self, implies_true]
  have nodup := by
    simp only [clause, List.nodup_nil]
  ⟨clause, nodupkey, nodup⟩

theorem empty_eq : toList (empty : DefaultClause n) = [] := rfl

def unit (l : Literal (PosFin n)) : DefaultClause n :=
  let clause := [l]
  have nodupkey : ∀ (l : PosFin n), ¬(l, true) ∈ clause ∨ ¬(l, false) ∈ clause := by
    intro l'
    by_cases l.2
    · apply Or.inr
      cases l
      simp_all [clause]
    · apply Or.inl
      cases l
      simp_all [clause]
  have nodup : List.Nodup clause:= by simp [clause]
  ⟨clause, nodupkey, nodup⟩

theorem unit_eq (l : Literal (PosFin n)) : toList (unit l) = [l] := rfl

def isUnit (c : DefaultClause n) : Option (Literal (PosFin n)) :=
  match c.clause with
  | [l] => some l
  | _ => none

theorem isUnit_iff (c : DefaultClause n) (l : Literal (PosFin n)) :
    isUnit c = some l ↔ toList c = [l] := by
  simp only [isUnit, toList]
  split
  · next l' heq => simp [heq]
  · next hne =>
    simp
    apply hne

def negate (c : DefaultClause n) : CNF.Clause (PosFin n) := c.clause.map Literal.negate

theorem negate_eq (c : DefaultClause n) : negate c = (toList c).map Literal.negate := rfl

/--
Attempts to add the literal `(idx, b)` to clause `c`. Returns none if doing so would make `c` a
tautology.
-/
def insert (c : DefaultClause n) (l : Literal (PosFin n)) : Option (DefaultClause n) :=
  if heq1 : c.clause.contains (l.1, !l.2) then
    none -- Adding l would make c a tautology
  else if heq2 : c.clause.contains l then
    some c
  else
    let clause := l :: c.clause
    have nodupkey : ∀ (l : PosFin n), ¬(l, true) ∈ clause ∨ ¬(l, false) ∈ clause := by
      intro l'
      simp only [List.contains, Bool.not_eq_true] at heq1
      simp only [List.find?, List.mem_cons, not_or, clause]
      by_cases l' = l.1
      · next l'_eq_l =>
        by_cases hl : l.2
        · apply Or.inr
          constructor
          · intro heq
            simp [← heq] at hl
          · simpa [hl, ← l'_eq_l] using heq1
        · simp only [Bool.not_eq_true] at hl
          apply Or.inl
          constructor
          · intro heq
            simp [← heq] at hl
          · simpa [hl, ← l'_eq_l] using heq1
      · next l'_ne_l =>
        have := c.nodupkey l'
        rcases c.nodupkey l' with h | h
        · left
          constructor
          · intro heq
            simp [← heq] at l'_ne_l
          · simp [h]
        · right
          constructor
          · intro heq
            simp [← heq] at l'_ne_l
          · simp [h]
    have nodup : List.Nodup clause := by
      simp only [List.elem_eq_mem, decide_eq_true_eq] at heq2
      simp [c.nodup, heq2, clause]
    some ⟨clause, nodupkey, nodup⟩

def ofArray (ls : Array (Literal (PosFin n))) : Option (DefaultClause n) :=
  let fold_fn (l : Literal (PosFin n)) (acc : Option (DefaultClause n)) : Option (DefaultClause n) :=
    match acc with
    | none => none
    | some acc => acc.insert l
  ls.foldr fold_fn (some empty)

theorem ofArray_eq (arr : Array (Literal (PosFin n)))
    (arrNodup : ∀ i : Fin arr.size, ∀ j : Fin arr.size, i.1 ≠ j.1 → arr[i] ≠ arr[j])
    (c : DefaultClause n) :
    ofArray arr = some c → toList c = Array.toList arr := by
  intro h
  simp only [ofArray] at h
  rw [toList]
  let motive (idx : Nat) (acc : Option (DefaultClause n)) : Prop :=
    ∃ idx_le_arr_size : idx ≤ arr.size, ∀ c' : DefaultClause n, acc = some c' →
      ∃ hsize : c'.clause.length = arr.size - idx, ∀ i : Fin c'.clause.length,
      have idx_in_bounds : idx + i.1 < arr.size := by
        omega
      List.get c'.clause i = arr[idx + i]'idx_in_bounds
  have h_base : motive arr.size (some empty) := by
    apply Exists.intro <| Nat.le_refl arr.size
    intro c' heq
    simp only [Option.some.injEq] at heq
    have hsize : List.length c'.clause = arr.size- arr.size := by
      simp [← heq, empty]
    apply Exists.intro hsize
    intro i
    simp only [← heq, empty, List.length_nil] at i
    exact Fin.elim0 i
  let fold_fn (l : Literal (PosFin n)) (acc : Option (DefaultClause n)) : Option (DefaultClause n) :=
    match acc with
    | none => none
    | some acc => acc.insert l
  have h_inductive (idx : Fin arr.size) (acc : Option (DefaultClause n)) (ih : motive (idx.1 + 1) acc) :
    motive idx.1 (fold_fn arr[idx] acc) := by
    rcases ih with ⟨idx_add_one_le_arr_size, ih⟩
    apply Exists.intro <| Nat.le_of_succ_le idx_add_one_le_arr_size
    intro c' heq
    simp only [Fin.getElem_fin, fold_fn] at heq
    split at heq
    · simp at heq
    · next acc =>
      specialize ih acc rfl
      rcases ih with ⟨hsize, ih⟩
      simp only at ih
      simp only [insert] at heq
      split at heq
      · simp at heq
      · split at heq
        · next h_dup =>
          exfalso -- h_dup contradicts arrNodup
          simp only [List.contains] at h_dup
          rcases List.get_of_mem <| List.mem_of_elem_eq_true h_dup with ⟨j, hj⟩
          specialize ih j
          rw [hj] at ih
          have idx_add_one_add_j_in_bounds : idx.1 + 1 + j.1 < arr.size := by
            omega
          have idx_ne_idx_add_one_add_j_in_bounds : idx.1 ≠ idx.1 + 1 + j.1 := by
            omega
          exact arrNodup idx ⟨idx.1 + 1 + j.1, idx_add_one_add_j_in_bounds⟩ idx_ne_idx_add_one_add_j_in_bounds ih
        · simp only [Option.some.injEq] at heq
          have hsize' : c'.clause.length = arr.size - idx.1 := by
            simp only [← heq, List.length_cons, hsize]
            omega
          apply Exists.intro hsize'
          intro i
          simp only
          have lhs_rw : c'.clause = arr[idx.1] :: acc.clause := by rw [← heq]
          simp only [List.get_of_eq lhs_rw]
          by_cases i.1 = 0
          · next i_eq_zero =>
            simp only [List.length_cons, i_eq_zero, List.get, Nat.add_zero]
          · next i_ne_zero =>
            rcases Nat.exists_eq_succ_of_ne_zero i_ne_zero with ⟨j, hj⟩
            simp only [List.length_cons, hj, List.get, Nat.succ_eq_add_one]
            simp only [Nat.add_comm j 1, ← Nat.add_assoc]
            exact ih ⟨j, by omega⟩
  rcases (Array.foldr_induction motive h_base h_inductive).2 c h with ⟨hsize, h⟩
  ext
  next i l =>
  by_cases i_in_bounds : i < c.clause.length
  · specialize h ⟨i, i_in_bounds⟩
    have i_in_bounds' : i < arr.toList.length := by
      dsimp; omega
    rw [List.getElem?_eq_getElem i_in_bounds, List.getElem?_eq_getElem i_in_bounds']
    simp only [List.get_eq_getElem, Nat.zero_add] at h
    rw [← Array.getElem_eq_getElem_toList]
    simp [h]
  · have arr_data_length_le_i : arr.toList.length ≤ i := by
      dsimp; omega
    simp only [Nat.not_lt, ← List.getElem?_eq_none_iff] at i_in_bounds arr_data_length_le_i
    rw [i_in_bounds, arr_data_length_le_i]

def delete (c : DefaultClause n) (l : Literal (PosFin n)) : DefaultClause n :=
  let clause := c.clause.erase l
  let nodupkey : ∀ (l : PosFin n), ¬(l, true) ∈ clause ∨ ¬(l, false) ∈ clause := by
    intro l'
    simp only [clause]
    rcases c.nodupkey l' with ih | ih
    · apply Or.inl
      intro h
      exact ih <| List.mem_of_mem_erase h
    · apply Or.inr
      intro h
      exact ih <| List.mem_of_mem_erase h
  have nodup := by
    simp only [clause]
    exact List.Nodup.erase l c.nodup
  ⟨clause, nodupkey, nodup⟩

theorem delete_iff (c : DefaultClause n) (l l' : Literal (PosFin n)) :
    l' ∈ toList (delete c l) ↔ l' ≠ l ∧ l' ∈ toList c := by
  simp only [toList, delete, ne_eq]
  by_cases hl : l' = l
  · simp only [hl, not_true, false_and, iff_false]
    exact List.Nodup.not_mem_erase c.nodup
  · simp only [hl, not_false_eq_true, true_and]
    exact List.mem_erase_of_ne hl

def contains (c : DefaultClause n) (l : Literal (PosFin n)) : Bool := c.clause.contains l

theorem contains_iff :
    ∀ (c : DefaultClause n) (l : Literal (PosFin n)), contains c l = true ↔ l ∈ toList c := by
  intro c l
  simp only [contains, List.contains]
  constructor
  · exact List.mem_of_elem_eq_true
  · exact List.elem_eq_true_of_mem

def reduce_fold_fn (assignments : Array Assignment) (acc : ReduceResult (PosFin n))
    (l : Literal (PosFin n)) :
    ReduceResult (PosFin n) :=
  match acc with
    | .encounteredBoth => .encounteredBoth
    | .reducedToEmpty =>
      match assignments[l.1.1]! with
      | .pos =>
        if l.2 then
          .reducedToUnit l
        else
          .reducedToEmpty
      | .neg =>
        if !l.2 then
          .reducedToUnit l
        else
          .reducedToEmpty
      | .both => .encounteredBoth
      | .unassigned => .reducedToUnit l
    | .reducedToUnit l' =>
      match assignments[l.1.1]! with
      | .pos =>
        if l.2 then
          .reducedToNonunit -- Assignment fails to refute both l and l'
        else
          .reducedToUnit l'
      | .neg =>
        if !l.2 then
          .reducedToNonunit -- Assignment fails to refute both l and l'
        else
          .reducedToUnit l'
      | .both => .encounteredBoth
      | .unassigned => .reducedToNonunit -- Assignments fails to refute both l and l'
    | .reducedToNonunit => .reducedToNonunit

/--
The `reduce` function takes in a clause `c` and takes in an array of assignments and attempts to
eliminate every literal in the clause that is not compatible with the `assignments` argument.
- If `reduce` returns `encounteredBoth`, then this means that the `assignments` array has a `both`
  Assignment and is therefore fundamentally unsatisfiable.
- If `reduce` returns `reducedToEmpty`, then this means that every literal in `c` is incompatible
  with `assignments`. In other words, this means that the conjunction of `assignments` and `c` is
  unsatisfiable.
- If `reduce` returns `reducedToUnit l`, then this means that every literal in `c` is incompatible
  with `assignments` except for `l`. In other words, this means that the conjunction of
  `assignments` and `c` entail `l`.
- If `reduce` returns `reducedToNonunit`, then this means that there are multiple literals in `c`
  that are compatible with `assignments`. This is a failure condition for `confirmRupHint`
  (in `LRAT.Formula.Implementation.lean`) which calls `reduce`. -/
def reduce (c : DefaultClause n) (assignments : Array Assignment) : ReduceResult (PosFin n) :=
  c.clause.foldl (reduce_fold_fn assignments) .reducedToEmpty

instance : Clause (PosFin n) (DefaultClause n) where
  toList := toList
  not_tautology := not_tautology
  ofArray := ofArray
  ofArray_eq := ofArray_eq
  empty := empty
  empty_eq := empty_eq
  unit := unit
  unit_eq := unit_eq
  isUnit := isUnit
  isUnit_iff := isUnit_iff
  negate := negate
  negate_eq := negate_eq
  insert := insert
  delete := delete
  delete_iff := delete_iff
  contains := contains
  contains_iff := contains_iff
  reduce := reduce

end DefaultClause

end Internal
end LRAT
end Std.Tactic.BVDecide
