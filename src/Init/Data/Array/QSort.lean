/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Ord

namespace Array
-- TODO: remove the [Inhabited α] parameters as soon as we have the tactic framework for automating proof generation and using Array.fget

def qpartition (as : Array α) (lt : α → α → Bool) (lo hi : Nat) : Nat × Array α :=
  if h : as.size = 0 then (0, as) else have : Inhabited α := ⟨as[0]'(by revert h; cases as.size <;> simp)⟩ -- TODO: remove
  let mid := (lo + hi) / 2
  let as  := if lt (as.get! mid) (as.get! lo) then as.swap! lo mid else as
  let as  := if lt (as.get! hi)  (as.get! lo) then as.swap! lo hi  else as
  let as  := if lt (as.get! mid) (as.get! hi) then as.swap! mid hi else as
  let pivot := as.get! hi
  let rec loop (as : Array α) (i j : Nat) :=
    if h : j < hi then
      if lt (as.get! j) pivot then
        let as := as.swap! i j
        loop as (i+1) (j+1)
      else
        loop as i (j+1)
    else
      let as := as.swap! i hi
      (i, as)
    termination_by hi - j
    decreasing_by all_goals simp_wf; decreasing_trivial_pre_omega
  loop as lo lo

@[inline] partial def qsort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1) : Array α :=
  let rec @[specialize] sort (as : Array α) (low high : Nat) :=
    if low < high then
      let p := qpartition as lt low high;
      -- TODO: fix `partial` support in the equation compiler, it breaks if we use `let (mid, as) := partition as lt low high`
      let mid := p.1
      let as  := p.2
      if mid >= high then as
      else
        let as := sort as low mid
        sort as (mid+1) high
    else as
  sort as low high

set_option linter.unusedVariables.funArgs false in
/--
Sort an array using `compare` to compare elements.
-/
def qsortOrd [ord : Ord α] (xs : Array α) : Array α :=
  xs.qsort fun x y => compare x y |>.isLT

end Array
