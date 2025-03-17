/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Nat.Linear
import Init.NotationExtra

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

theorem Array.of_push_eq_push {as bs : Array α} (h : as.push a = bs.push b) : as = bs ∧ a = b := by
  simp only [push, mk.injEq] at h
  have ⟨h₁, h₂⟩ := List.of_concat_eq_concat h
  cases as; cases bs
  simp_all

private theorem List.size_toArrayAux (as : List α) (bs : Array α) : (as.toArrayAux bs).size = as.length + bs.size := by
  induction as generalizing bs with
  | nil => simp [toArrayAux]
  | cons a as ih => simp +arith [toArrayAux, *]

private theorem List.of_toArrayAux_eq_toArrayAux {as bs : List α} {cs ds : Array α} (h : as.toArrayAux cs = bs.toArrayAux ds) (hlen : cs.size = ds.size) : as = bs ∧ cs = ds := by
  match as, bs with
  | [], []    => simp [toArrayAux] at h; simp [h]
  | a::as, [] => simp [toArrayAux] at h; rw [← h] at hlen; simp +arith [size_toArrayAux] at hlen
  | [], b::bs => simp [toArrayAux] at h; rw [h] at hlen; simp +arith [size_toArrayAux] at hlen
  | a::as, b::bs =>
    simp [toArrayAux] at h
    have : (cs.push a).size = (ds.push b).size := by simp [*]
    have ⟨ih₁, ih₂⟩ := of_toArrayAux_eq_toArrayAux h this
    simp [ih₁]
    have := Array.of_push_eq_push ih₂
    simp [this]

theorem List.toArray_eq_toArray_eq (as bs : List α) : (as.toArray = bs.toArray) = (as = bs) := by
  simp

/--
Applies the monadic action `f` to every element in the array, left-to-right, and returns the array
of results. Furthermore, the resulting array's type guarantees that it contains the same number of
elements as the input array.
-/
def Array.mapM' [Monad m] (f : α → m β) (as : Array α) : m { bs : Array β // bs.size = as.size } :=
  go 0 ⟨mkEmpty as.size, rfl⟩ (by simp)
where
  go (i : Nat) (acc : { bs : Array β // bs.size = i }) (hle : i ≤ as.size) : m { bs : Array β // bs.size = as.size } := do
    if h : i = as.size then
      return h ▸ acc
    else
      have hlt : i < as.size := Nat.lt_of_le_of_ne hle h
      let b ← f as[i]
      go (i+1) ⟨acc.val.push b, by simp [acc.property]⟩ hlt
  termination_by as.size - i
  decreasing_by decreasing_trivial_pre_omega

@[inline] private unsafe def mapMonoMImp [Monad m] (as : Array α) (f : α → m α) : m (Array α) :=
  go 0 as
where
  @[specialize] go (i : Nat) (as : Array α) : m (Array α) := do
    if h : i < as.size then
      let a := as[i]
      let b ← f a
      if ptrEq a b then
        go (i+1) as
      else
        go (i+1) (as.set i b h)
    else
      return as

/--
Applies a monadic function to each element of an array, returning the array of results. The function is
monomorphic: it is required to return a value of the same type. The internal implementation uses
pointer equality, and does not allocate a new array if the result of each function call is
pointer-equal to its argument.
-/
@[implemented_by mapMonoMImp] def Array.mapMonoM [Monad m] (as : Array α) (f : α → m α) : m (Array α) :=
  as.mapM f

/--
Applies a function to each element of an array, returning the array of results. The function is
monomorphic: it is required to return a value of the same type. The internal implementation uses
pointer equality, and does not allocate a new array if the result of each function call is
pointer-equal to its argument.
-/
@[inline] def Array.mapMono (as : Array α) (f : α → α) : Array α :=
  Id.run <| as.mapMonoM f
