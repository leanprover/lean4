/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Jungmann and Johan Henkel
-/
module

prelude
public import Init.Data.Vector.Basic
public import Init.Data.Ord.Basic
import Init.Omega

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- We do not enable `linter.indexVariables` because it is helpful to name index variables `sllo`, `slhi`, etc.


/-
  Simple implementation of insertion sort as a cutoff for small slices
-/
def insertionSort [Ord α]
  (xs : Vector α size) (sllo slhi i : Nat)
  (hslloslhi : sllo < slhi) (hslhi : slhi ≤ size)
  (hslloi : sllo ≤ i) (hslhii : i ≤ slhi)
  : Vector α size :=

  if hfin : i = slhi then xs else

  let rec movedown [Ord α] (xs : Vector α size) (j : Nat) (hjsllo : sllo ≤ j) (hjslhi : j < slhi) : Vector α size :=

    if hfin : j = sllo then xs else

    if compare (xs[j]) (xs[j - 1]) = .lt then
      movedown (xs.swap j (j - 1)) (j - 1) (by omega) (by omega)
    else xs

  insertionSort (movedown xs i (by omega) (by omega)) sllo slhi (i + 1) (by omega) (by omega) (by omega) (by omega)

/-
  Selects the median of three in the given slice [sllo...slhi)
-/
def pivotselect [Ord α]
  (xs : Vector α size) (sllo slhi : Nat)
  (hslhi : slhi ≤ size) (hslloslhi : sllo < slhi)
  : {idx : Nat // sllo ≤ idx ∧ idx < slhi} :=

  let p1 := xs[sllo]
  let p2 := xs[sllo + (slhi - sllo)/2]
  let p3 := xs[slhi - 1]

  let le := fun a b => compare a b != .gt

  if le p1 p2 then
    if le p2 p3 then ⟨sllo + (slhi - sllo)/2, (by omega)⟩
    else if le p1 p3 then ⟨slhi - 1, (by omega)⟩
    else ⟨sllo, (by omega)⟩

  else
    if le p1 p3 then ⟨sllo, (by omega)⟩
    else if le p2 p3 then ⟨slhi - 1, (by omega)⟩
    else ⟨sllo + (slhi - sllo)/2, (by omega)⟩

/-
  Second stage of dnf algorithm
    pivot is in the eq-partition, therefore the other two slices that will need further sorting must be smaller than the original one
-/
def dnfstage2 [Ord α]
  (xs : Vector α size) (pvt eq unproc fin_unproc sllo slhi : Nat)
  (heq_unproc : eq < unproc) (hunproc_fin_unproc : unproc ≤ fin_unproc) (hfin_unproc : fin_unproc < size)
  (hsllo : sllo ≤ eq) (hfin_unproc_slhi : fin_unproc < slhi) (hlohi : slhi - sllo > 1) (hslhi : slhi ≤ size)
  (hpvt_sllo : sllo ≤ pvt) (hpvt_slhi : pvt < slhi) (hpvt_eq : eq ≤ pvt) (hpvt_fin_unproc : pvt ≤ fin_unproc)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

  match compare xs[unproc] xs[pvt] with
  | .lt =>
    if hfin : unproc ≥ fin_unproc then ⟨((xs.swap unproc eq), eq + 1, fin_unproc + 1), by simp; omega⟩ else
    if hpvt : eq = pvt then dnfstage2 (xs.swap unproc eq) unproc (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    if compare xs[eq] xs[unproc] = .lt then dnfstage2 xs pvt (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    dnfstage2 (xs.swap unproc eq) pvt (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .gt =>
    if hfin : unproc ≥ fin_unproc then ⟨(xs, eq, fin_unproc), by simp; omega⟩ else
    if hpvt : fin_unproc = pvt then dnfstage2 (xs.swap unproc fin_unproc) unproc eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    if compare xs[fin_unproc] xs[unproc] = .gt then dnfstage2 xs pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    else dnfstage2 (xs.swap unproc fin_unproc) pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .eq =>
    if hfin : unproc ≥ fin_unproc then ⟨(xs, eq, fin_unproc + 1), by simp; omega⟩ else
    dnfstage2 xs pvt eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-
  First stage of dnf algorithm: partitions until the pivot is in the eq-partition
    During both stages, the following partitioning scheme applies:
      [sllo...eq) - elements smaller than the pivot
      [eq...unproc) - elements that are equal to the pivot
      [unproc...fin_unproc] - elements that have not been processed yet
      [fin_unproc + 1...slhi) - elements that are greater than the pivot
-/
def dnfstage1 [Ord α]
  (xs : Vector α size) (pvt eq unproc fin_unproc sllo slhi : Nat)
  (heq_unproc : eq ≤ unproc) (hunproc_fin_unproc : unproc ≤ fin_unproc) (hfin_unproc : fin_unproc < size)
  (hsllo : sllo ≤ eq) (hfin_unproc_slhi : fin_unproc < slhi) (hlohi : slhi - sllo > 1) (hslhi : slhi ≤ size)
  (hpvt_sllo : sllo ≤ pvt) (hpvt_slhi : pvt < slhi) (hpvt_unproc : unproc ≤ pvt) (hpvt_fin_unproc : pvt ≤ fin_unproc)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

  if hpvt : unproc = pvt then
    if hfin : fin_unproc = unproc then ⟨(xs, eq, fin_unproc + 1), by simp; omega⟩
    else dnfstage2 xs pvt eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  else match compare xs[unproc] xs[pvt] with
  | .lt =>
    dnfstage1 (xs.swap eq unproc) pvt (eq+1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .gt =>
    if hfin : fin_unproc = unproc then ⟨(xs, eq, fin_unproc), by simp; omega⟩ else
    if hfin2 : fin_unproc - unproc = 1 then ⟨(xs.swap unproc fin_unproc, eq, fin_unproc), by simp; omega⟩ else
    if hpvt2 : pvt = fin_unproc then dnfstage2 (xs.swap unproc pvt) unproc eq (unproc + 1) (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) else
    dnfstage1 (xs.swap unproc fin_unproc) pvt eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

  | .eq =>
    dnfstage2 xs pvt eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-
  Wrapper for the two-staged Dutch National Flag algorithm
    returns (xs, mid, hi) and some proofs so that xs is partitioned as follows:
      [sllo...mid) --- elements smaller than the pivot
      [mid...hi) -- elements equal to the pivot
      [hi...slhi) - elemts that are greater than the pivot
-/
@[inline]
def dnfstaged [Ord α]
  (xs : Vector α size) (pvt : Nat) (sllo slhi : Nat)
  (hlohi : slhi - sllo > 1) (hhi : slhi ≤ size)
  (hpvt : sllo ≤ pvt ∧ pvt < slhi)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

  dnfstage1 xs pvt sllo sllo (slhi - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-
  Main algorithm
-/
def quicksorthelper [Ord α]
  (xs : Vector α  size) (sllo slhi : Nat)
  (hslloslhi : sllo ≤ slhi) (hslhi : slhi ≤ size)
  : Vector α size :=

  if hfin : slhi - sllo ≤ 1 then xs else

  if slhi - sllo ≤ 16 then insertionSort xs sllo slhi (sllo + 1) (by omega) (by omega) (by omega) (by omega) else

  let pvt := pivotselect xs sllo slhi (by omega) (by omega)
  let ⟨(ys, mid, hi), ⟨h1, h2, h3⟩⟩ := (dnfstaged xs pvt sllo slhi (by omega) (by omega) (by omega))


  have hterm : slhi - hi < slhi - sllo := by simp only [] at h1 h2 h3; omega
  let ys' := quicksorthelper ys hi slhi (by omega) (by omega)

  have hterm2 : mid - sllo < slhi - sllo := by simp only [] at h1 h2 h3; omega
  quicksorthelper ys' sllo mid (by omega) (by omega)

termination_by slhi - sllo


/-
  Uses a lt function to create a Ord instance for the actual algorithm
    Necessary for compatibility reasons
-/
@[inline, reducible]
def ordOfLt (lt : α → α → Bool) : Ord α where
  compare a b :=
    if lt a b then .lt
    else if lt b a then .gt
    else .eq

/-
  Wrappers for qsort to ensure compatibility to previous code
-/
def Array.qsort (xs : Array α) (lt : α → α → Bool := by exact (· < ·)) (sllo := 0) (slhi := xs.size) : Array α :=
  letI : Ord α := ordOfLt lt
  let slhi := min slhi xs.size
  let sllo := min sllo slhi
  (quicksorthelper xs.toVector sllo slhi (by omega) (by omega)).toArray

def Vector.qsort {size} (xs : Vector α size) (lt : α → α → Bool := by exact (· < ·)) (sllo := 0) (slhi := size) : Vector α size :=
  letI : Ord α := ordOfLt lt
  let slhi := min slhi size
  let sllo := min sllo slhi
  quicksorthelper xs sllo slhi (by omega) (by omega)

def Array.qsortOrd [Ord α] (xs : Array α) (sllo := 0) (slhi := xs.size - 1) : Array α :=
  let slhi := min slhi xs.size
  let sllo := min sllo slhi
  (quicksorthelper xs.toVector sllo slhi (by omega) (by omega)).toArray

def Vector.qsortOrd [Ord α] {size} (xs : Vector α size) (sllo := 0) (slhi := size) : Vector α size :=
  let slhi := min slhi size
  let sllo := min sllo slhi
  quicksorthelper xs sllo slhi (by omega) (by omega)
