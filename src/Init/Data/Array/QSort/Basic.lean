/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ?
-/
module

prelude
public import Init.Data.Vector.Basic
public import Init.Data.Ord.Basic
import Init.Omega

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`vecay`/`Vector` variables.
-- We do not enable `linter.indexVariables` because it is helpful to name index variables `lo`, `mid`, `hi`, etc.



def insertionSort [Ord α]
  (xs : Vector α size) (lo hi i : Nat)
  (hlohi : lo < hi) (hhi : hi ≤ size)
  (hilo : lo ≤ i) (hihi : i ≤ hi)
  : Vector α size :=

  if hfin : i = hi then xs else

  let rec movedown [Ord α] (xs : Vector α size) (j : Nat) (hjlo : lo ≤ j) (hjhi : j < hi) : Vector α size :=

    if hfin : j = lo then xs else

    if compare (xs[j]) (xs[j - 1]) = .lt then

      movedown (xs.swap j (j - 1)) (j - 1) (by omega) (by omega)

    else xs

  insertionSort (movedown xs i (by omega) (by omega)) lo hi (i + 1) (by omega) (by omega) (by omega) (by omega)


def pivotselect [Ord α]
  (xs : Vector α size) (lo hi : Nat)
  (hhi : hi ≤ size) (hlohi : lo < hi)
  : {idx : Nat // lo ≤ idx ∧ idx < hi} :=

  let p1 := xs[lo]
  let p2 := xs[lo + (hi - lo)/2]
  let p3 := xs[hi - 1]

  let le := fun a b => compare a b != .gt

  if le p1 p2 then
    if le p2 p3 then ⟨lo + (hi - lo)/2, (by omega)⟩
    else if le p1 p3 then ⟨hi - 1, (by omega)⟩
    else ⟨lo, (by omega)⟩

  else
    if le p1 p3 then ⟨lo, (by omega)⟩
    else if le p2 p3 then ⟨hi - 1, (by omega)⟩
    else ⟨lo + (hi - lo)/2, (by omega)⟩


def dnfhelper [Ord α]
  (xs : Vector α size) (eq unproc fin_unproc : Nat) (sllo slhi : Nat)
  (heq_unproc : eq < unproc) (hunproc_fin_unproc : unproc ≤ fin_unproc) (hfin_unproc : fin_unproc < size)
  (hsllo : sllo ≤ eq) (hfin_unproc_slhi : fin_unproc < slhi) (hlohi : slhi - sllo > 1) (hslhi : slhi ≤ size)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

    match compare xs[unproc] xs[eq] with

    | .lt =>
      if hfin : unproc ≥ fin_unproc then ⟨((xs.swap unproc eq (by omega) (by omega)), eq + 1, fin_unproc + 1), (by simp; omega)⟩ else
      if compare xs[eq] xs[unproc] = .lt then dnfhelper xs  (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)  else
      dnfhelper (xs.swap unproc eq (by omega) (by omega))  (eq + 1) (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

    | .gt =>
      if hfin : unproc ≥ fin_unproc then ⟨(xs, eq, fin_unproc), (by simp; omega)⟩ else
      if compare xs[fin_unproc] xs[unproc] = .gt then dnfhelper xs  eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)  else
      dnfhelper (xs.swap unproc fin_unproc (by omega) (by omega))  eq unproc (fin_unproc - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

    | .eq =>
      if hfin : unproc ≥ fin_unproc then ⟨(xs, eq, fin_unproc + 1), (by simp; omega)⟩ else
      dnfhelper xs  eq (unproc + 1) fin_unproc sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


def dnf [Ord α] -- wrapper
  (xs : Vector α size) (pvt : Nat) (sllo slhi : Nat)
  (hlohi : slhi - sllo > 1) (hhi : slhi ≤ size)
  (hpvt : sllo ≤ pvt ∧ pvt < slhi)
  : {r : (Vector α size × Nat × Nat) // r.snd.snd ≤ slhi ∧ sllo ≤ r.snd.fst ∧ r.snd.fst ≤ size ∧ r.snd.fst < r.snd.snd} :=

  dnfhelper (xs.swap pvt sllo) sllo (sllo+1) (slhi - 1) sllo slhi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)


def quicksorthelper [Ord α]
  (xs : Vector α  size) (sllo slhi : Nat)
  (hslloslhi : sllo ≤ slhi) (hslhi : slhi ≤ size)
  : Vector α size :=

  if hfin : slhi - sllo ≤ 1 then xs else
  if slhi - sllo ≤ 16 then insertionSort xs sllo slhi (sllo + 1) (by omega) (by omega) (by omega) (by omega) else
  let pvt := pivotselect xs sllo slhi (by omega) (by omega)
  let ⟨(xs', mid, hi), ⟨h1, h2, h3, h4⟩⟩ := dnf xs pvt sllo slhi (by omega) (by omega) (by omega)

  have hterm : slhi - hi < slhi - sllo := by
    simp only [] at h1 h2 h3 h4
    omega
  let ys := quicksorthelper xs' hi slhi (by omega) (by omega)
  have hterm2 : mid - sllo < slhi - sllo := by
    simp only [] at h1 h2 h3 h4
    omega
  quicksorthelper ys sllo mid (by omega) (by omega)

termination_by slhi - sllo


def Array.quicksort2 [Ord α]  --wrapper
  (xs : Array α)
  : Array α :=

  (quicksorthelper xs.toVector 0 xs.size (by omega) (by omega)).toArray


def Vector.quicksort2 [Ord α]  {size}
  (xs : Vector α size)
  : Vector α size :=

  quicksorthelper xs 0 size (by omega) (by omega)
