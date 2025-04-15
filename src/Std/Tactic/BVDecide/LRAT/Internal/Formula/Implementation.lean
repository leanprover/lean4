/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Formula.Class
import Std.Tactic.BVDecide.LRAT.Internal.Assignment
import Std.Sat.CNF.Basic

/-!
This module contains the default implementation of the `Formula` typeclass that is used in the
surface level LRAT checker.
-/

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

open Std.Sat
open Assignment DefaultClause ReduceResult

/--
The structure `DefaultFormula n` takes in a parameter `n` which is intended to be one greater than the total number of variables that
can appear in the formula (hence why the parameter `n` is called `numVarsSucc` below). The structure has 4 fields:
- The `clauses` field maintains the total set of clauses that appear in the formula. Additionally, when a default formula is created
  by parsing a CNF file and modified by a series of LRAT additions and deletions, the following informal invariant is maintained:
  1. `clauses[0]` is always set to `none`.
  2. The m clauses in the original CNF file are stored in indices 1 through m of the `clauses` field (and they are stored in the order
     in which they appear in the CNF file).
  3. Each subsequent LRAT addition is pushed to the very end of the `clauses` array, even if there are elements in the current array set
     to none.
  4. When a clause index is deleted via `delete`, that index in `clauses` is set to `none`

  The purpose of this invariant is to preserve a 1-to-1 correspondence between indices referenced by any external LRAT proof and the internal
  indices used within `clauses`

- The `rupUnits` field is empty except during the processing of RUP additions and RAT additions. During a RUP addition or a RAT addition, the
  `rupUnits` field is used to store negated units from the clause being evaluated for the addition. Regardless of whether the addition is
  successful, the `rupUnits` field is cleared prior to returning. The reason that `rupUnits` is included as part of the default formula
  structure (as opposed to simply being an Array that is passed through the helper functions relating to RUP and RAT additions) is to simplify
  the semantics of default formulas. Since `rupUnits` is part of the default formula structure, it can be taken into account in the `toList`
  function that defines its satisfiability semantics, making it possible to "add" negated units to a default formula and have it affect its
  semantics in an easily reversible manner.

- The `ratUnits` field is empty except during the processing of RAT additions. This field serves an extremely similar role to `rupUnits` in that
  it is used to temporarily store negated units during unit propagation. The primary difference between the `rupUnits` field and `ratUnits` field
  is that the `rupUnits` field is only updated twice for each RUP or RAT addition (once to add negated units and then once again to remove said
  negated units), the `ratUnits` field is updated zero times for each RUP addition and updated m times for each RAT addition where m is the number
  of negative hints in said RAT addition (i.e. the number of clauses in the formula containing the RAT addition's negated pivot literal).

- The `assignments` field is maintained to quickly look up which values (if any) are entailed for a variable by the formula. At most points in time,
  (i.e. at all points in time except during a RUP or RAT addition), the `assignments` field must satisfy the `StrongAssignmentsInvariant` defined
  in Formula.Lemmas.lean. During RUP and RAT additions, the `assignments` field must satisfy the `AssignmentsInvariant` defined in Formula.Lemmas.lean.
  The reason that the `assignments` field is contained as an explicit part of the default formula (as opposed to simply being an Array that is passed
  through the helper functions concerning unit propagation), is so that the (potentially large) Array does not need to repeatedly be allocated and
  deallocated. By having the `assignments` Array be a field of the default formula, it is easier to ensure that the Array is used linearly.
-/
@[ext] structure DefaultFormula (numVarsSucc : Nat) where
  clauses : Array (Option (DefaultClause numVarsSucc))
  rupUnits : Array (Literal (PosFin numVarsSucc))
    -- Used to store unit clauses that are only added for the duration of a rup check
  ratUnits : Array (Literal (PosFin numVarsSucc))
    -- Used to store unit clauses that are only added for the duration of a rat check
  assignments : Array Assignment

namespace DefaultFormula

instance {n : Nat} : Inhabited (DefaultFormula n) where
  default := ⟨#[], #[], #[], Array.replicate n unassigned⟩

/-- Note: This function is only for reasoning about semantics. Its efficiency doesn't actually matter -/
def toList {n : Nat} (f : DefaultFormula n) : List (DefaultClause n) :=
  (f.clauses.toList.filterMap id) ++ (f.rupUnits.toList.map unit) ++ (f.ratUnits.toList.map unit)

def ofArray_fold_fn (assignments : Array Assignment) (cOpt : Option (DefaultClause n)) :
    Array Assignment :=
  match cOpt with
  | none => assignments
  | some c =>
    match isUnit c with
    | none => assignments
    | some (l, true) => assignments.modify l addPosAssignment
    | some (l, false) => assignments.modify l addNegAssignment

/--
Note: This function assumes that the provided `clauses` Array is indexed according to the `clauses`
field invariant described in the DefaultFormula doc comment.
-/
def ofArray {n : Nat} (clauses : Array (Option (DefaultClause n))) : DefaultFormula n :=
  let assignments := clauses.foldl ofArray_fold_fn (Array.replicate n unassigned)
  ⟨clauses, #[], #[], assignments⟩

def insert {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) : DefaultFormula n :=
  let ⟨clauses, rupUnits, ratUnits, assignments⟩ := f
  match isUnit c with
    | none => ⟨clauses.push c, rupUnits, ratUnits, assignments⟩
    | some (l, true) => ⟨clauses.push c, rupUnits, ratUnits, assignments.modify l addPosAssignment⟩
    | some (l, false) => ⟨clauses.push c, rupUnits, ratUnits, assignments.modify l addNegAssignment⟩

def deleteOne {n : Nat} (f : DefaultFormula n) (id : Nat) : DefaultFormula n :=
  let ⟨clauses, rupUnits, ratUnits, assignments⟩ := f
  match clauses[id]! with
    | none => ⟨clauses, rupUnits, ratUnits, assignments⟩
    | some ⟨[l], _, _⟩ =>
      ⟨clauses.set! id none, rupUnits, ratUnits, assignments.modify l.1 (removeAssignment l.2)⟩
    | some _ => ⟨clauses.set! id none, rupUnits, ratUnits, assignments⟩

def delete {n : Nat} (f : DefaultFormula n) (ids : Array Nat) : DefaultFormula n :=
  ids.foldl (fun f id => f.deleteOne id) f

instance {n : Nat} : Entails (PosFin n) (DefaultFormula n) where
  eval := fun p f => (toList f).all (fun s => p ⊨ s)

theorem formulaEntails_def {n : Nat} (p : (PosFin n) → Bool) (f : DefaultFormula n) :
  Entails.eval p f = (toList f).all (fun c => p ⊨ c) := Eq.refl (p ⊨ f)

def insertUnit : Array (Literal (PosFin n)) × Array Assignment × Bool →
    Literal (PosFin n) → Array (Literal (PosFin n)) × Array Assignment × Bool :=
  fun (units, assignments, foundContradiction) (l, b) =>
    let curAssignment := assignments[l.1]!
    if hasAssignment b curAssignment then
      (units, assignments, foundContradiction)
    else
      let units := units.push (l, b)
      let assignments := assignments.modify l (addAssignment b)
      let foundContradiction := foundContradiction || curAssignment != unassigned
      (units, assignments, foundContradiction)

/--
Returns an updated formula f and a bool which indicates whether a contradiction was found in the
process of updating f.
-/
def insertRupUnits {n : Nat} (f : DefaultFormula n) (ls : CNF.Clause (PosFin n)) :
    DefaultFormula n × Bool :=
  let ⟨clauses, rupUnits, ratUnits, assignments⟩ := f
  let (rupUnits, assignments, foundContradiction) := ls.foldl insertUnit (rupUnits, assignments, false)
  (⟨clauses, rupUnits, ratUnits, assignments⟩, foundContradiction)

/--
Returns an updated formula f and a bool which indicates whether a contradiction was found in the
process of updating f.
-/
def insertRatUnits {n : Nat} (f : DefaultFormula n) (ls : CNF.Clause (PosFin n)) : DefaultFormula n × Bool :=
  let ⟨clauses, rupUnits, ratUnits, assignments⟩ := f
  let (ratUnits, assignments, foundContradiction) := ls.foldl insertUnit (ratUnits, assignments, false)
  (⟨clauses, rupUnits, ratUnits, assignments⟩, foundContradiction)

def clearUnit : Array Assignment → Literal (PosFin n) → Array Assignment
  | assignments, (l, b) => assignments.modify l (removeAssignment b)

def clearRupUnits {n : Nat} (f : DefaultFormula n) : DefaultFormula n :=
  let ⟨clauses, rupUnits, ratUnits, assignments⟩ := f
  let assignments := rupUnits.foldl clearUnit assignments
  -- TODO: in principle we could cache the memory of rupUnits here if we had Array.clear
  ⟨clauses, #[], ratUnits, assignments⟩

def clearRatUnits {n : Nat} (f : DefaultFormula n) : DefaultFormula n :=
  let ⟨clauses, rupUnits, ratUnits, assignments⟩ := f
  let assignments := ratUnits.foldl clearUnit assignments
  -- TODO: in principle we could cache the memory of ratUnits here if we had Array.clear
  ⟨clauses, rupUnits, #[], assignments⟩

/--
Reverts assignments to the array it was prior to adding derivedLits.
-/
def restoreAssignments {n : Nat} (assignments : Array Assignment) (derivedLits : List (PosFin n × Bool)) :
    Array Assignment :=
  derivedLits.foldl clearUnit assignments

/--
The fold function used for performRupCheck.
-/
def confirmRupHint {n : Nat} (clauses : Array (Option (DefaultClause n))) :
    Array Assignment × CNF.Clause (PosFin n) × Bool × Bool → Nat →
    Array Assignment × CNF.Clause (PosFin n) × Bool × Bool :=
  fun (assignments, derivedLits, derivedEmpty, encounteredError) id =>
    if (encounteredError || derivedEmpty) then
      (assignments, derivedLits, derivedEmpty, encounteredError)
    else
      match clauses[id]? with
      | some (some c) =>
        match c.reduce assignments with
        | encounteredBoth => (assignments, derivedLits, true, false) -- derivedEmpty (by discovering there was already a contradiction)
        | reducedToEmpty => (assignments, derivedLits, true, false) -- derivedEmpty
        | reducedToUnit (l, b) =>
          if hasAssignment b assignments[l.1]! then -- Don't add (l, b) to derivedLits because we already knew it
            (assignments, derivedLits, false, false)
          else
            (assignments.modify l (addAssignment b), (l, b) :: derivedLits, false, false)
        | reducedToNonunit => (assignments, derivedLits, false, true) -- encounteredError
      | some none => (assignments, derivedLits, false, true) -- encounteredError
      | none => (assignments, derivedLits, false, true) -- encounteredError

/--
Takes in a formula f and an array of rupHints and attempts to verify that f is unsatisfiable. It returns:
- f', which is the same as f but the assignments field has been updated to be consistent with anything learned over the
  course of the rupCheck
- derivedLits, which is the list of literals that were derived over the course of the rupCheck (these are needed to
  eventually reconstruct the original assignment)
- derivedEmpty, which indicates whether the empty clause or a contradiction was derived
- encounteredError, which is true if the rupCheck failed and false otherwise

Note: This function assumes that any rupUnits and ratUnits corresponding to this rup check have already been added to f.
-/
def performRupCheck {n : Nat} (f : DefaultFormula n) (rupHints : Array Nat) :
    DefaultFormula n × CNF.Clause (PosFin n) × Bool × Bool :=
  let ⟨clauses, rupUnits, ratUnits, assignments⟩ := f
  let (assignments, derivedLits, derivedEmpty, encounteredError) := rupHints.foldl (confirmRupHint clauses) (assignments, [], false, false)
  (⟨clauses, rupUnits, ratUnits, assignments⟩, derivedLits, derivedEmpty, encounteredError)

/--
Attempts to verify that c can be added to f via unit propagation. If it can, it returns
`((f.insert c), true)`. If it can't, it returns false as the second part of the tuple
(and no guarantees are made about what formula is returned).
-/
def performRupAdd {n : Nat} (f : DefaultFormula n) (c : DefaultClause n) (rupHints : Array Nat) :
    DefaultFormula n × Bool :=
  let negC := negate c
  let (f, foundContradiction) := insertRupUnits f negC
  if foundContradiction then
    let f := clearRupUnits f
    (f.insert c, true)
  else
    let (f, derivedLits, derivedEmpty, encounteredError) := performRupCheck f rupHints
    if encounteredError then
      (f, false)
    else if !derivedEmpty then
      (f, false)
    else -- derivedEmpty is true and encounteredError is false
      let ⟨clauses, rupUnits, ratUnits, assignments⟩ := f
      let assignments := restoreAssignments assignments derivedLits
      -- assignments should now be the same as it was before the performRupCheck call
      let f := clearRupUnits ⟨clauses, rupUnits, ratUnits, assignments⟩
      -- f should now be the same as it was before insertRupUnits
      (f.insert c, true)

/-- Returns an array of indices corresponding to clauses that contain the negation of l -/
def getRatClauseIndices {n : Nat} (clauses : Array (Option (DefaultClause n)))
    (l : Literal (PosFin n)) :
    Array Nat :=
  let negL := Literal.negate l
  let filter_fn := fun i =>
    match clauses[i]! with
    | none => false
    | some c => c.contains negL
  (Array.range clauses.size).filter filter_fn

/--
Checks that for each clause `c ∈ f` such that `(Literal.negate pivot) ∈ c`, `c`'s index is in
`ratHints.map (fun x => x.1)`. This function assumes that ratHints are ordered by the value of their
first argument, which is consistent with LRAT's specification
-/
def ratHintsExhaustive {n : Nat} (f : DefaultFormula n) (pivot : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat)) :
    Bool :=
  let ratClauseIndices := getRatClauseIndices f.clauses pivot
  let ratHintIndices := ratHints.map (fun x => x.1) -- This doesn't use ratHints linearly ratHints shouldn't be large
  ratClauseIndices = ratHintIndices

/--
Takes in a formula `f` and a single `ratHint` and attempts to verify that `f` is inconsistent with the
negation of the `ratHint`'s clause. It returns:
- `f` which is the same as the original `f` (including the ratUnits and assignment fields)
  - Although the `ratUnits` and `assignments` fields are updated during the procedure,
    they are restored prior to returning..
- `success`, which indicates whether empty was successfully derived without any errors

Note: This function assumes that the `ratUnits` corresponding to this rat check have NOT already
been added to `f`. In terms of input expectations and output guarantees, this function is more
analogous to `performRupAdd` than `performRupCheck`.
-/
def performRatCheck {n : Nat} (f : DefaultFormula n) (negPivot : Literal (PosFin n))
    (ratHint : Nat × Array Nat) :
    DefaultFormula n × Bool :=
  match f, ratHint with
  | ⟨clauses, rupUnits, ratUnits, assignments⟩, (id, rupHints) =>
    match clauses[id]! with
    | some c =>
      let negC := negate <| c.delete negPivot
      let (f, foundContradiction) := insertRatUnits ⟨clauses, rupUnits, ratUnits, assignments⟩ negC
      if foundContradiction then
        let f := clearRatUnits f
        (f, true)
      else
        let (f, derivedLits, derivedEmpty, encounteredError) := performRupCheck f rupHints
        match f with
        | ⟨clauses, rupUnits, ratUnits, assignments⟩ =>
          let assignments := restoreAssignments assignments derivedLits
          -- assignments should now be the same as it was before the performRupCheck call
          let f := clearRatUnits ⟨clauses, rupUnits, ratUnits, assignments⟩
          -- f should now be the same as it was before insertRatUnits
          if encounteredError || !derivedEmpty then (f, false)
          else (f, true)
    | none => (⟨clauses, rupUnits, ratUnits, assignments⟩, false)

/--
Attempts to verify that `c` can be added to `f` via unit propagation. If it can, it returns
`((f.insert c), true)`. If it can't, it returns false as the second part of the tuple
(and no guarantees are made about what formula is returned).
-/
def performRatAdd {n : Nat} (f : DefaultFormula n) (c : DefaultClause n)
    (pivot : Literal (PosFin n)) (rupHints : Array Nat) (ratHints : Array (Nat × Array Nat)) :
    DefaultFormula n × Bool :=
  if ratHintsExhaustive f pivot ratHints then
    let negC := negate c
    let (f, contradictionFound) := insertRupUnits f negC
    if contradictionFound then (f, false) -- This should be a rupAdd rather than a ratAdd
    else
      let (f, derivedLits, derivedEmpty, encounteredError) := performRupCheck f rupHints
      if encounteredError then (f, false)
      else if derivedEmpty then (f, false) -- This should be a rupAdd rather than a ratAdd
      else -- derivedEmpty is false and encounteredError is false
        let fold_fn := fun (f, allChecksPassed) ratHint =>
          if allChecksPassed then performRatCheck f (Literal.negate pivot) ratHint
          else (f, false)
        let (f, allChecksPassed) := ratHints.foldl fold_fn (f, true)
        if !allChecksPassed then (f, false)
        else
          match f with
          | ⟨clauses, rupUnits, ratUnits, assignments⟩ =>
            let assignments := restoreAssignments assignments derivedLits
            -- assignments should now be the same as it was before the performRupCheck call
            let f := clearRupUnits ⟨clauses, rupUnits, ratUnits, assignments⟩
            -- f should now be the same as it was before insertRupUnits
            (f.insert c, true)
  else (f, false)

def numClausesInFormula {n : Nat} (f : DefaultFormula n) : Nat := Id.run do
  let mut numClauses := 0
  for cOpt in f.clauses do
    if cOpt != none then
      numClauses := numClauses + 1
  return numClauses

end DefaultFormula

end Internal
end LRAT
end Std.Tactic.BVDecide
