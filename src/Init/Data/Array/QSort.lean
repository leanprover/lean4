/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Omega

namespace Array

@[inline] def qpartition (as : {as : Array α // as.size = n})
    (lt : α → α → Bool) (lo hi : Fin n) (hle : lo ≤ hi) :
    {as : Array α // as.size = n} × {pivot : Fin n // lo ≤ pivot ∧ pivot ≤ hi} :=
  let mid : Fin n := ⟨(lo.1 + hi) / 2, by omega⟩
  let rec @[inline] maybeSwap (as : {as : Array α // as.size = n}) (lo hi : Fin n) : {as : Array α // as.size = n} :=
    let hi := hi.cast as.2.symm
    let lo := lo.cast as.2.symm
    if lt (as.1.get hi) (as.1.get lo) then ⟨as.1.swap lo hi, (Array.size_swap ..).trans as.2⟩ else as
  let as := maybeSwap as lo mid
  let as := maybeSwap as lo hi
  let as := maybeSwap as hi mid
  let_fun pivot := as.1.get (hi.cast as.2.symm)
  let rec loop
      (as : {as : Array α // as.size = n}) (i j : Fin n) (H : lo ≤ i ∧ i ≤ j ∧ j ≤ hi) :
      {as : Array α // as.size = n} × {pivot : Fin n // lo ≤ pivot ∧ pivot ≤ hi} :=
    have ⟨loi, ij, jhi⟩ := H
    if h : j < hi then by
      -- FIXME: if we don't clear these variables, `omega` will revert/intro them
      -- and as a result `loop` will spuriously depend on the extra `as` variables, breaking linearity
      rename_i as₁ as₂ as₃ as₄; clear as₁ mid as₂ as₃ as₄
      exact if lt (as.1.get (j.cast as.2.symm)) pivot then
        let as := ⟨as.1.swap (i.cast as.2.symm) (j.cast as.2.symm), (Array.size_swap ..).trans as.2⟩
        loop as ⟨i.1+1, by omega⟩ ⟨j.1+1, by omega⟩
          ⟨Nat.le_succ_of_le H.1, Nat.succ_le_succ ij, Nat.succ_le_of_lt h⟩
      else
        loop as i ⟨j.1+1, by omega⟩ ⟨loi, Nat.le_succ_of_le ij, Nat.succ_le_of_lt h⟩
    else
      let as := ⟨as.1.swap (i.cast as.2.symm) (hi.cast as.2.symm), (Array.size_swap ..).trans as.2⟩
      ⟨as, i, loi, Nat.le_trans ij jhi⟩
  termination_by hi.1 - j
  loop as lo lo ⟨Nat.le_refl _, Nat.le_refl _, hle⟩

@[inline] def qsort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1) : Array α :=
  let rec @[specialize] sort {n} (as : {as : Array α // as.size = n})
      (lo : Nat) (hi : Fin n) : {as : Array α // as.size = n} :=
    if h : lo < hi.1 then
      let ⟨as, mid, (_ : lo ≤ mid), _⟩ :=
        qpartition as lt ⟨lo, Nat.lt_trans h hi.2⟩ hi (Nat.le_of_lt h)
      let as := sort as lo ⟨mid - 1, by omega⟩
      sort as (mid + 1) hi
    else as
  termination_by hi - lo
  if low < high then
    if h : high < as.size then
      (sort ⟨as, rfl⟩ low ⟨high, h⟩).1
    else
      have := Inhabited.mk as
      panic! "index out of bounds"
  else as

end Array
