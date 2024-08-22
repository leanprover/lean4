/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Init.ByCases
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Entails
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.PosFin

namespace Lean.Elab.Tactic.BVDecide
namespace LRAT
namespace Internal

/--
The `Assignment` inductive datatype is used in the `assignments` field of default formulas (defined in
Formula.Implementation.lean) to store and quickly access information about whether unit literals are
contained in (or entailed by) a formula.

The elements of `Assignment` can be viewed as a lattice where `both` is top, satisfying both `hasPosAssignment`
and `hasNegAssignment`, `pos` satisfies only the former, `neg` satisfies only the latter, and `unassigned` is
bottom, satisfying neither. If one wanted to modify the default formula structure to use a BitArray rather than
an `Assignment Array` for the `assignments` field, a reasonable 2-bit representation of the `Assignment` type
would be:
- both: 11
- pos: 10
- neg: 01
- unassigned: 00

Then `hasPosAssignment` could simply query the first bit and `hasNegAssignment` could simply query the second bit.
-/
inductive Assignment
  | pos
  | neg
  | both
  | unassigned
deriving Inhabited, DecidableEq, BEq

namespace Assignment

instance : ToString Assignment where
  toString := fun a =>
    match a with
    | pos => "pos"
    | neg => "neg"
    | both => "both"
    | unassigned => "unassigned"

def hasPosAssignment (assignment : Assignment) : Bool :=
  match assignment with
  | pos => true
  | neg => false
  | both => true
  | unassigned => false

def hasNegAssignment (assignment : Assignment) : Bool :=
  match assignment with
  | pos => false
  | neg => true
  | both => true
  | unassigned => false

/--
Updates the old assignment of `l` to reflect the fact that `(l, true)` is now part of the formula.
-/
def addPosAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => pos
  | neg => both
  | both => both
  | unassigned => pos

/--
Updates the old assignment of `l` to reflect the fact that `(l, true)` is no longer part of the
formula.
-/
def removePosAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => unassigned
  | neg => neg -- Note: This case should not occur
  | both => neg
  | unassigned => unassigned -- Note: this case should not occur

/--
Updates the old assignment of `l` to reflect the fact that `(l, false)` is now part of the formula.
-/
def addNegAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => both
  | neg => neg
  | both => both
  | unassigned => neg

/--
Updates the old assignment of `l` to reflect the fact that `(l, false)` is no longer part of the
formula.
-/
def removeNegAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => pos -- Note: This case should not occur
  | neg => unassigned
  | both => pos
  | unassigned => unassigned -- Note: This case should not occur

def addAssignment (b : Bool) : Assignment → Assignment :=
  if b then
    addPosAssignment
  else
    addNegAssignment

def removeAssignment (b : Bool) : Assignment → Assignment :=
  if b then
    removePosAssignment
  else
    removeNegAssignment

def hasAssignment (b : Bool) : Assignment → Bool :=
  if b then
    hasPosAssignment
  else
    hasNegAssignment

theorem removePos_addPos_cancel {assignment : Assignment} (h : ¬(hasPosAssignment assignment)) :
  removePosAssignment (addPosAssignment assignment) = assignment := by
  rw [removePosAssignment, addPosAssignment]
  rw [hasPosAssignment] at h
  cases assignment <;> simp_all

theorem removeNeg_addNeg_cancel {assignment : Assignment} (h : ¬(hasNegAssignment assignment)) :
  removeNegAssignment (addNegAssignment assignment) = assignment := by
  rw [removeNegAssignment, addNegAssignment]
  rw [hasNegAssignment] at h
  cases assignment <;> simp_all

theorem remove_add_cancel {assignment : Assignment} {b : Bool} (h : ¬(hasAssignment b assignment)) :
  removeAssignment b (addAssignment b assignment) = assignment := by
  by_cases hb : b
  · simp only [removeAssignment, hb, addAssignment, ite_true]
    simp only [hasAssignment, hb, ite_true] at h
    exact removePos_addPos_cancel h
  · simp only [removeAssignment, hb, addAssignment, ite_true]
    simp only [hasAssignment, hb, ite_false] at h
    exact removeNeg_addNeg_cancel h

theorem add_both_eq_both (b : Bool) : addAssignment b both = both := by
  rw [addAssignment]
  split <;> decide

theorem has_both (b : Bool) : hasAssignment b both = true := by
  rw [hasAssignment]
  split <;> decide

theorem has_add (assignment : Assignment) (b : Bool) :
    hasAssignment b (addAssignment b assignment) := by
  rw [addAssignment, hasAssignment]
  split
  · rw [hasPosAssignment, addPosAssignment]
    cases assignment <;> simp
  · rw [hasNegAssignment, addNegAssignment]
    cases assignment <;> simp

theorem not_hasPos_removePos (assignment : Assignment) :
    ¬hasPosAssignment (removePosAssignment assignment) := by
  simp only [removePosAssignment, hasPosAssignment, Bool.not_eq_true]
  cases assignment <;> simp

theorem not_hasNeg_removeNeg (assignment : Assignment) :
    ¬hasNegAssignment (removeNegAssignment assignment) := by
  simp only [removeNegAssignment, hasNegAssignment, Bool.not_eq_true]
  cases assignment <;> simp

theorem not_has_remove (assignment : Assignment) (b : Bool) :
    ¬hasAssignment b (removeAssignment b assignment) := by
  by_cases hb : b
  · have h := not_hasPos_removePos assignment
    simp [hb, h, removeAssignment, hasAssignment]
  · have h := not_hasNeg_removeNeg assignment
    simp [hb, h, removeAssignment, hasAssignment]

theorem has_remove_irrelevant (assignment : Assignment) (b : Bool) :
    hasAssignment b (removeAssignment (!b) assignment) → hasAssignment b assignment := by
  by_cases hb : b
  · simp only [hb, removeAssignment, Bool.not_true, ite_false, hasAssignment, ite_true]
    cases assignment <;> decide
  · simp only [Bool.not_eq_true] at hb
    simp only [hb, removeAssignment, Bool.not_true, ite_false, hasAssignment, ite_true]
    cases assignment <;> decide

theorem unassigned_of_has_neither (assignment : Assignment) (lacks_pos : ¬(hasPosAssignment assignment))
  (lacks_neg : ¬(hasNegAssignment assignment)) :
  assignment = unassigned := by
  simp only [hasPosAssignment, Bool.not_eq_true] at lacks_pos
  split at lacks_pos <;> simp_all (config := { decide := true })

theorem hasPos_addNeg (assignment : Assignment) :
    hasPosAssignment (addNegAssignment assignment) = hasPosAssignment assignment := by
  rw [hasPosAssignment, addNegAssignment]
  cases assignment <;> simp (config := { decide := true })

theorem hasNeg_addPos (assignment : Assignment) :
    hasNegAssignment (addPosAssignment assignment) = hasNegAssignment assignment := by
  rw [hasNegAssignment, addPosAssignment]
  cases assignment <;> simp (config := { decide := true })

theorem has_iff_has_add_complement (assignment : Assignment) (b : Bool) :
    hasAssignment b assignment ↔ hasAssignment b (addAssignment (¬b) assignment) := by
  by_cases hb : b <;> simp [hb, hasAssignment, addAssignment, hasPos_addNeg, hasNeg_addPos]

theorem addPos_addNeg_eq_both (assignment : Assignment) :
    addPosAssignment (addNegAssignment assignment) = both := by
  rw [addPosAssignment, addNegAssignment]
  cases assignment <;> simp

theorem addNeg_addPos_eq_both (assignment : Assignment) :
    addNegAssignment (addPosAssignment assignment) = both := by
  rw [addNegAssignment, addPosAssignment]
  cases assignment <;> simp

instance {n : Nat} : Entails (PosFin n) (Array Assignment) where
  eval := fun p arr => ∀ i : PosFin n, ¬(hasAssignment (¬p i) arr[i.1]!)

end Assignment

end Internal
end LRAT
end Lean.Elab.Tactic.BVDecide
