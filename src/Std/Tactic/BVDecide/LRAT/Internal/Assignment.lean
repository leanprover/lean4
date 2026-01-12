/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.Entails
public import Std.Tactic.BVDecide.LRAT.Internal.PosFin
public import Init.Grind

@[expose] public section

namespace Std.Tactic.BVDecide
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

attribute [local grind cases] Assignment

instance : ToString Assignment where
  toString := fun a =>
    match a with
    | pos => "pos"
    | neg => "neg"
    | both => "both"
    | unassigned => "unassigned"

@[inline]
def hasPosAssignment (assignment : Assignment) : Bool :=
  match assignment with
  | pos => true
  | neg => false
  | both => true
  | unassigned => false

@[inline]
def hasNegAssignment (assignment : Assignment) : Bool :=
  match assignment with
  | pos => false
  | neg => true
  | both => true
  | unassigned => false

/--
Updates the old assignment of `l` to reflect the fact that `(l, true)` is now part of the formula.
-/
@[inline]
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
@[inline]
def removePosAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => unassigned
  | neg => neg -- Note: This case should not occur
  | both => neg
  | unassigned => unassigned -- Note: this case should not occur

/--
Updates the old assignment of `l` to reflect the fact that `(l, false)` is now part of the formula.
-/
@[inline]
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
@[inline]
def removeNegAssignment (oldAssignment : Assignment) : Assignment :=
  match oldAssignment with
  | pos => pos -- Note: This case should not occur
  | neg => unassigned
  | both => pos
  | unassigned => unassigned -- Note: This case should not occur

attribute [local grind] hasPosAssignment hasNegAssignment addNegAssignment addPosAssignment
  removePosAssignment removeNegAssignment

def addAssignment (b : Bool) (a : Assignment) : Assignment :=
  if b then
    addPosAssignment a
  else
    addNegAssignment a

def removeAssignment (b : Bool) (a : Assignment) : Assignment :=
  if b then
    removePosAssignment a
  else
    removeNegAssignment a

def hasAssignment (b : Bool) (a : Assignment) : Bool :=
  if b then
    hasPosAssignment a
  else
    hasNegAssignment a

attribute [local grind] addAssignment removeAssignment hasAssignment

theorem removePos_addPos_cancel {assignment : Assignment} (h : ¬(hasPosAssignment assignment)) :
  removePosAssignment (addPosAssignment assignment) = assignment := by grind

theorem removeNeg_addNeg_cancel {assignment : Assignment} (h : ¬(hasNegAssignment assignment)) :
  removeNegAssignment (addNegAssignment assignment) = assignment := by grind

theorem remove_add_cancel {assignment : Assignment} {b : Bool} (h : ¬(hasAssignment b assignment)) :
  removeAssignment b (addAssignment b assignment) = assignment := by grind

theorem add_both_eq_both (b : Bool) : addAssignment b both = both := by grind

theorem has_both (b : Bool) : hasAssignment b both = true := by grind

theorem has_add (assignment : Assignment) (b : Bool) :
    hasAssignment b (addAssignment b assignment) := by grind

theorem not_hasPos_removePos (assignment : Assignment) :
    ¬hasPosAssignment (removePosAssignment assignment) := by grind

theorem not_hasNeg_removeNeg (assignment : Assignment) :
    ¬hasNegAssignment (removeNegAssignment assignment) := by grind

theorem not_has_remove (assignment : Assignment) (b : Bool) :
    ¬hasAssignment b (removeAssignment b assignment) := by grind

theorem has_remove_irrelevant (assignment : Assignment) (b : Bool) :
    hasAssignment b (removeAssignment (!b) assignment) → hasAssignment b assignment := by grind

theorem unassigned_of_has_neither (assignment : Assignment) (lacks_pos : ¬(hasPosAssignment assignment))
  (lacks_neg : ¬(hasNegAssignment assignment)) :
  assignment = unassigned := by grind

@[local grind =]
theorem hasPos_addNeg (assignment : Assignment) :
    hasPosAssignment (addNegAssignment assignment) = hasPosAssignment assignment := by grind

@[local grind =]
theorem hasNeg_addPos (assignment : Assignment) :
    hasNegAssignment (addPosAssignment assignment) = hasNegAssignment assignment := by grind

theorem has_iff_has_add_complement (assignment : Assignment) (b : Bool) :
    hasAssignment b assignment ↔ hasAssignment b (addAssignment (¬b) assignment) := by grind

theorem addPos_addNeg_eq_both (assignment : Assignment) :
    addPosAssignment (addNegAssignment assignment) = both := by grind

theorem addNeg_addPos_eq_both (assignment : Assignment) :
    addNegAssignment (addPosAssignment assignment) = both := by grind

instance {n : Nat} : Entails (PosFin n) (Array Assignment) where
  eval := fun p arr => ∀ i : PosFin n, ¬(hasAssignment (¬p i) arr[i.1]!)

end Assignment

end Internal
end LRAT
end Std.Tactic.BVDecide
