/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Init.Data.List.Erase
import Init.Data.Array.Lemmas
import Std.Data.HashMap
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
  empty : β
  empty_eq : toList empty = []
  unit : Literal α → β
  unit_eq : ∀ l : Literal α, toList (unit l) = [l]
  isUnit : β → Option (Literal α)
  isUnit_iff : ∀ c : β, ∀ l : Literal α, isUnit c = some l ↔ toList c = [l]
  negate : β → CNF.Clause α
  negate_eq : ∀ c : β, negate c = (toList c).map Literal.negate
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

@[inline]
def empty : DefaultClause n :=
  let clause := []
  have nodupkey := by
    simp only [clause, List.find?, List.not_mem_nil, not_false_eq_true, or_self, implies_true]
  have nodup := by
    simp only [clause, List.nodup_nil]
  ⟨clause, nodupkey, nodup⟩

theorem empty_eq : toList (empty : DefaultClause n) = [] := rfl

@[inline]
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

@[inline]
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

@[inline]
def negate (c : DefaultClause n) : CNF.Clause (PosFin n) := c.clause.map Literal.negate

theorem negate_eq (c : DefaultClause n) : negate c = (toList c).map Literal.negate := rfl

def ofArray (ls : Array (Literal (PosFin n))) : Option (DefaultClause n) :=
  let mapOption := ls.foldl folder (some (HashMap.emptyWithCapacity ls.size))
  match mapOption with
  | none => none
  | some map =>
   have mapnodup := map.distinct_keys
    have nodupkey : ∀ (l : PosFin n), ¬(l, true) ∈ map.toList ∨ ¬(l, false) ∈ map.toList := by
      intro l
      apply Classical.byContradiction
      simp_all
    have nodup : map.toList.Nodup := by
      rw [List.Nodup, List.pairwise_iff_forall_sublist]
      simp only [ne_eq, Prod.forall, Bool.forall_bool, Prod.mk.injEq, not_and, Bool.not_eq_false,
        Bool.not_eq_true, Bool.false_eq_true, imp_false, implies_true, and_true, Bool.true_eq_false,
        true_and]
      intro l1
      constructor
      . intros l2 h hl
        rw [List.pairwise_iff_forall_sublist] at mapnodup
        replace h : [l1, l2].Sublist map.keys := by
          rw [← HashMap.map_fst_toList_eq_keys, List.sublist_map_iff]
          apply Exists.intro [(l1, false), (l2, false)]
          simp [h]
        specialize mapnodup h
        simp [hl] at mapnodup
      . intros l2 h hl
        rw [List.pairwise_iff_forall_sublist] at mapnodup
        replace h : [l1, l2].Sublist map.keys := by
          rw [← HashMap.map_fst_toList_eq_keys, List.sublist_map_iff]
          apply Exists.intro [(l1, true), (l2, true)]
          simp [h]
        specialize mapnodup h
        simp [hl] at mapnodup
    some ⟨map.toList, nodupkey, nodup⟩
where
  folder (acc : Option (Std.HashMap (PosFin n) Bool)) (l : Literal (PosFin n)) :
      Option (Std.HashMap (PosFin n) Bool) :=
    match acc with
    | none => none
    | some map =>
      let (val?, map) := map.getThenInsertIfNew? l.1 l.2
      if let some val' := val? then
        if l.2 != val' then
          none
        else
          some map
      else
        some map

@[simp]
theorem ofArray.foldl_folder_none_eq_none : List.foldl ofArray.folder none ls = none := by
  apply List.foldlRecOn (motive := (· = none))
  · simp
  · intro b hb a ha
    unfold DefaultClause.ofArray.folder
    simp [hb]

theorem ofArray.mem_of_mem_of_foldl_folder_eq_some
    (h : List.foldl DefaultClause.ofArray.folder (some acc) ls = some acc') :
    ∀ l ∈ acc.toList, l ∈ acc'.toList := by
  intro l hl
  induction ls generalizing acc with
  | nil => simp_all
  | cons x xs ih =>
    rcases l with ⟨var, pol⟩
    rw [List.foldl_cons, DefaultClause.ofArray.folder.eq_def] at h
    split at h
    · contradiction
    · simp only [HashMap.getThenInsertIfNew?_fst, HashMap.get?_eq_getElem?, bne_iff_ne, ne_eq,
        HashMap.getThenInsertIfNew?_snd, ite_not] at h
      split at h
      · split at h
        · apply ih
          · exact h
          · rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, Std.HashMap.getElem?_insertIfNew]
            rename_i map _ _ _ _ _
            have : x.fst ∈ map := by
              apply Classical.byContradiction
              intro h2
              have := Std.HashMap.getElem?_eq_none h2
              simp_all
            simp [this]
            rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hl
            simp_all
        · simp at h
      · apply ih
        · exact h
        · rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, Std.HashMap.getElem?_insertIfNew]
          simp_all
          intros
          cases pol <;> simp_all

theorem ofArray.folder_foldl_mem_of_mem
    (h : List.foldl DefaultClause.ofArray.folder acc ls = some map) :
    ∀ l ∈ ls, l ∈ map.toList := by
  intro l hl
  induction ls generalizing acc with
  | nil => simp at hl
  | cons x xs ih =>
    simp at hl h
    rcases hl with hl | hl
    · rw [DefaultClause.ofArray.folder.eq_def] at h
      simp at h
      split at h
      · simp at h
      · split at h
        · split at h
          · apply mem_of_mem_of_foldl_folder_eq_some
            · exact h
            · rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
              rw [Std.HashMap.getElem?_insertIfNew]
              simp_all
          · simp at h
        · apply mem_of_mem_of_foldl_folder_eq_some
          · exact h
          · next hfoo =>
            rw [hl]
            cases x
            simp [Std.HashMap.getElem?_insertIfNew]
            intro hbar
            exfalso
            apply hfoo
            rw [Std.HashMap.getElem?_eq_some_getElem! hbar]
    · exact ih h hl

@[inline]
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

@[inline]
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
  empty := empty
  empty_eq := empty_eq
  unit := unit
  unit_eq := unit_eq
  isUnit := isUnit
  isUnit_iff := isUnit_iff
  negate := negate
  negate_eq := negate_eq
  delete := delete
  delete_iff := delete_iff
  contains := contains
  contains_iff := contains_iff
  reduce := reduce

end DefaultClause

end Internal
end LRAT
end Std.Tactic.BVDecide
