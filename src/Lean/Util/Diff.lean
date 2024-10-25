/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
prelude
import Init.Data.Array.Subarray.Split
import Init.Data.Range
import Lean.Data.HashMap
import Std.Data.HashMap.Basic
import Init.Omega

namespace Lean.Diff
/--
An action in an edit script to transform one source sequence into a target sequence.
-/
inductive Action where
  /-- Insert the item into the source -/
  | insert
  /-- Delete the item from the source -/
  | delete
  /-- Leave the item in the source -/
  | skip
deriving Repr, BEq, Hashable, Repr

instance : ToString Action where
  toString
    | .insert => "insert"
    | .delete => "delete"
    | .skip => "skip"

/--
Determines a prefix to show on a given line when printing diff results.

For `delete`, the prefix is `"-"`, for `insert`, it is `"+"`, and for `skip` it is `" "`.
-/
def Action.linePrefix : (action : Action) → String
  | .delete => "-"
  | .insert => "+"
  | .skip => " "

/--
A histogram entry consists of the number of times the element occurs in the left and right input
arrays along with an index at which the element can be found, if applicable.
-/
structure Histogram.Entry (α : Type u) (lsize rsize : Nat) where
  /-- How many times the element occurs in the left array -/
  leftCount : Nat
  /-- An index of the element in the left array, if applicable -/
  leftIndex : Option (Fin lsize)
  /-- Invariant: the count is non-zero iff there is a saved index -/
  leftWF : leftCount = 0 ↔ leftIndex = none
  /-- How many times the element occurs in the right array -/
  rightCount : Nat
  /-- An index of the element in the right array, if applicable -/
  rightIndex : Option (Fin rsize)
  /-- Invariant: the count is non-zero iff there is a saved index -/
  rightWF : rightCount = 0 ↔ rightIndex = none

/-- A histogram for arrays maps each element to a count and, if applicable, an index.-/
def Histogram (α : Type u) (lsize rsize : Nat) [BEq α] [Hashable α] :=
  Std.HashMap α (Histogram.Entry α lsize rsize)


section

variable [BEq α] [Hashable α]

/-- Add an element from the left array to a histogram -/
def Histogram.addLeft (histogram : Histogram α lsize rsize) (index : Fin lsize) (val : α)
    : Histogram α lsize rsize :=
  match histogram.get? val with
  | none => histogram.insert val {
      leftCount := 1, leftIndex := some index,
      leftWF := by simp,
      rightCount := 0, rightIndex := none
      rightWF := by simp
    }
  | some x => histogram.insert val {x with
      leftCount := x.leftCount + 1, leftIndex := some index, leftWF := by simp
    }

/-- Add an element from the right array to a histogram -/
def Histogram.addRight (histogram : Histogram α lsize rsize) (index : Fin rsize) (val : α)
    : Histogram α lsize rsize :=
  match histogram.get? val with
  | none => histogram.insert val {
      leftCount := 0, leftIndex := none,
      leftWF := by simp,
      rightCount := 1, rightIndex := some index,
      rightWF := by simp
    }
  | some x => histogram.insert val {x with
      rightCount := x.leftCount + 1, rightIndex := some index,
      rightWF := by simp
    }

/-- Given two `Subarray`s, find their common prefix and return their differing suffixes -/
def matchPrefix (left right : Subarray α) : Array α × Subarray α × Subarray α :=
  let rec go (pref : Array α) : Array α × Subarray α × Subarray α :=
    let i := pref.size
    if _ : i < left.size ∧ i < right.size then
      if left[i]'(by omega) == right[i]'(by omega) then
        go <| pref.push <| left[i]'(by omega)
      else (pref, left.drop pref.size, right.drop pref.size)
    else (pref, left.drop pref.size, right.drop pref.size)
  termination_by left.size - pref.size
  go #[]


/-- Given two `Subarray`s, find their common suffix and return their differing prefixes -/
def matchSuffix (left right : Subarray α) : Subarray α × Subarray α × Array α :=
  let rec go (i : Nat) : Subarray α × Subarray α × Array α :=
    if _ : i < left.size ∧ i < right.size then
      if left[left.size - i - 1]'(by omega) == right[right.size - i - 1]'(by omega) then
        go i.succ
      else
        (left.take (left.size - i), right.take (right.size - i), (left.drop (left.size - i)).toArray)
    else
      (left.take (left.size - i), right.take (right.size - i), (left.drop (left.size - i)).toArray)
    termination_by left.size - i
  go 0

/--
Finds the least common subsequence of two arrays using a variant of jgit's histogram diff algorithm.

Unlike jgit's implementation, this one does not perform a cutoff on histogram bucket sizes, nor does
it fall back to the Myers diff algorithm. This means that it has quadratic worst-case complexity.
Empirically, however, even quadratic cases of this implementation can handle hundreds of megabytes
in a second or so, and it is intended to be used for short strings like error messages. Be
cautious when applying it to larger workloads.
-/
partial def lcs (left right : Subarray α) : Array α := Id.run do
  let (pref, left, right) := matchPrefix left right
  let (left, right, suff) := matchSuffix left right
  let mut hist : Histogram α left.size right.size := .empty
  for h : i in [0:left.size] do
    hist := hist.addLeft ⟨i, Membership.get_elem_helper h rfl⟩ left[i]
  for h : i in [0:right.size] do
    hist := hist.addRight ⟨i, Membership.get_elem_helper h rfl⟩ right[i]
  let mut best := none
  for (k, v) in hist.toList do
    if let {leftCount := lc, leftIndex := some li, rightCount := rc, rightIndex := some ri, ..} := v then
      match best with
      | none =>
        best := some ((lc + rc), k, li, ri)
      | some (count, _) =>
        if lc + rc < count then
          best := some ((lc + rc), k, li, ri)
  let some (_, v, li, ri) := best
    | return pref ++ suff

  let lefts := left.split ⟨li.val, by cases li; omega⟩
  let rights := right.split ⟨ri.val, by cases ri; omega⟩

  pref ++ lcs lefts.1 rights.1 ++ #[v] ++ lcs (lefts.2.drop 1) (rights.2.drop 1) ++ suff

/--
Computes an edit script to transform `left` into `right`.
-/
def diff [Inhabited α] (original edited : Array α) : Array (Action × α) :=
  if h : ¬(0 < original.size) then
    edited.map (.insert, ·)
  else if h' : ¬(0 < edited.size) then
    original.map (.delete, ·)
  else Id.run do
    have : original.size > 0 := by omega
    have : edited.size > 0 := by omega
    let mut out := #[]
    let ds := lcs original.toSubarray edited.toSubarray
    let mut i := 0
    let mut j := 0
    for d in ds do
      while i < original.size && original[i]! != d do
        out := out.push <| (.delete, original[i]!)
        i := i.succ
      while j < edited.size && edited[j]! != d do
        out := out.push <| (.insert, edited[j]!)
        j := j.succ
      out := out.push <| (.skip, d)
      i := i.succ
      j := j.succ
    while h : i < original.size do
      out := out.push <| (.delete, original[i])
      i := i.succ
    while h : j < edited.size do
      out := out.push <| (.insert, edited[j])
      j := j.succ
    out

/-- Shows a line-by-line edit script with markers for added and removed lines. -/
def linesToString [ToString α] (lines : Array (Action × α)) : String := Id.run do
  let mut out : String := ""
  for (act, line) in lines do
    let lineStr := toString line
    if lineStr == "" then
      out := out ++ s!"{act.linePrefix}\n"
    else
      out := out ++ s!"{act.linePrefix} {lineStr}\n"
  out
