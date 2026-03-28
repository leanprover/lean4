/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
module
prelude
public import Std.Data.HashMap
public import Std.Sat.CNF.Basic
public import Std.Tactic.BVDecide.LRAT.Internal.Assignment
import Init.Data.List.Erase
import Init.Data.List.Pairwise
@[expose] public section

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

grind_pattern empty_eq => toList (empty : β)
grind_pattern unit_eq => @toList _ _ self (unit l)
attribute [grind =] isUnit_iff negate_eq delete_iff
attribute [grind ←] contains_iff

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
  nodupkey : ∀ l : PosFin numVarsSucc, (l, true) ∉ clause ∨ (l, false) ∉ clause := by grind
  nodup : List.Nodup clause := by grind
  deriving BEq

instance : ToString (DefaultClause n) where
  toString c := s!"{c.clause.reverse}"

namespace DefaultClause

@[grind] def toList (c : DefaultClause n) : CNF.Clause (PosFin n) := c.clause

attribute [local grind! ←] DefaultClause.nodup DefaultClause.nodupkey

theorem not_tautology (c : DefaultClause n) (l : Literal (PosFin n)) :
    l ∉ toList c ∨ ¬Literal.negate l ∈ toList c := by
  grind [cases Bool]

@[inline]
def empty : DefaultClause n where
  clause := []

theorem empty_eq : toList (empty : DefaultClause n) = [] := rfl

@[inline]
def unit (l : Literal (PosFin n)) : DefaultClause n where
  clause := [l]

theorem unit_eq (l : Literal (PosFin n)) : toList (unit l) = [l] := rfl

@[inline]
def isUnit (c : DefaultClause n) : Option (Literal (PosFin n)) :=
  match c.clause with
  | [l] => some l
  | _ => none

theorem isUnit_iff (c : DefaultClause n) (l : Literal (PosFin n)) :
    isUnit c = some l ↔ toList c = [l] := by
  grind [isUnit]

@[inline]
def negate (c : DefaultClause n) : CNF.Clause (PosFin n) := c.clause.map Literal.negate

theorem negate_eq (c : DefaultClause n) : negate c = (toList c).map Literal.negate := rfl

@[irreducible] def ofArray.folder (acc : Option (Std.HashMap (PosFin n) Bool)) (l : Literal (PosFin n)) :
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

-- Recall `@[local grind]` doesn't work for theorems in namespaces,
-- so we add the attribute after the fact.
attribute [local grind] DefaultClause.ofArray.folder

-- This isn't a good global `grind` lemma, because it can cause a loop with `Pairwise.sublist`.
attribute [local grind =] List.pairwise_iff_forall_sublist

def ofArray (ls : Array (Literal (PosFin n))) : Option (DefaultClause n) :=
  let mapOption := ls.foldl ofArray.folder (some (HashMap.emptyWithCapacity ls.size))
  match mapOption with
  | none => none
  | some map =>
    have mapnodup := map.distinct_keys
    some { clause := map.toList }

@[simp]
theorem ofArray.foldl_folder_none_eq_none : List.foldl ofArray.folder none ls = none := by
  apply List.foldlRecOn (motive := (· = none)) <;> grind

attribute [local grind =] ofArray.foldl_folder_none_eq_none

theorem ofArray.mem_of_mem_of_foldl_folder_eq_some
    (h : List.foldl DefaultClause.ofArray.folder (some acc) ls = some acc') (l) (h : l ∈ acc.toList) :
      l ∈ acc'.toList := by
  induction ls generalizing acc with grind

grind_pattern ofArray.mem_of_mem_of_foldl_folder_eq_some => l ∈ acc'.toList, List.foldl ofArray.folder (some acc) ls

theorem ofArray.folder_foldl_mem_of_mem
    (h : List.foldl DefaultClause.ofArray.folder acc ls = some map) :
    ∀ l ∈ ls, l ∈ map.toList := by
  intro l hl
  induction ls generalizing acc with
  | nil => grind
  | cons x xs ih =>
    simp at hl h
    rcases hl <;> grind [DefaultClause.ofArray.folder.eq_def]

@[inline, local grind]
def delete (c : DefaultClause n) (l : Literal (PosFin n)) : DefaultClause n where
  clause := c.clause.erase l

theorem delete_iff (c : DefaultClause n) (l l' : Literal (PosFin n)) :
    l' ∈ toList (delete c l) ↔ l' ≠ l ∧ l' ∈ toList c := by
  grind

@[inline]
def contains (c : DefaultClause n) (l : Literal (PosFin n)) : Bool := c.clause.contains l

theorem contains_iff :
    ∀ (c : DefaultClause n) (l : Literal (PosFin n)), contains c l = true ↔ l ∈ toList c := by
  grind [contains]

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
