/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

prelude
import all Init.Data.List.OfFn
import Init.Data.List.Monadic

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/--
Lists all elements of `Fin n` in order, starting at `0`.

Examples:
 * `List.finRange 0 = ([] : List (Fin 0))`
 * `List.finRange 2 = ([0, 1] : List (Fin 2))`
-/
def finRange (n : Nat) : List (Fin n) := ofFn fun i => i

@[simp, grind =] theorem length_finRange {n : Nat} : (List.finRange n).length = n := by
  simp [List.finRange]

@[simp, grind =] theorem getElem_finRange {i : Nat} (h : i < (List.finRange n).length) :
    (finRange n)[i] = Fin.cast length_finRange ⟨i, h⟩ := by
  simp [List.finRange]

@[simp, grind =] theorem finRange_zero : finRange 0 = [] := by simp [finRange]

theorem finRange_succ {n} : finRange (n+1) = 0 :: (finRange n).map Fin.succ := by
  apply List.ext_getElem; simp; intro i; cases i <;> simp

theorem finRange_succ_last {n} :
    finRange (n+1) = (finRange n).map Fin.castSucc ++ [Fin.last n] := by
  apply List.ext_getElem
  · simp
  · intros
    simp only [List.finRange, List.getElem_ofFn, getElem_append, length_map, length_ofFn,
      getElem_map, Fin.castSucc_mk, getElem_singleton]
    split
    · rfl
    · next h => exact Fin.eq_last_of_not_lt h

@[grind _=_]
theorem finRange_reverse {n} : (finRange n).reverse = (finRange n).map Fin.rev := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv => lhs; rw [finRange_succ_last]
    conv => rhs; rw [finRange_succ]
    rw [reverse_append, reverse_cons, reverse_nil, nil_append, singleton_append, ← map_reverse,
      map_cons, ih, map_map, map_map]
    congr; funext
    simp [Fin.rev_succ]

end List

namespace Fin

@[grind =] theorem foldlM_eq_foldlM_finRange [Monad m] (f : α → Fin n → m α) (x : α) :
    foldlM n f x = (List.finRange n).foldlM f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    simp [foldlM_succ, List.finRange_succ, List.foldlM_cons]
    congr 1
    funext y
    simp [ih, List.foldlM_map]

@[grind =] theorem foldrM_eq_foldrM_finRange [Monad m] [LawfulMonad m] (f : Fin n → α → m α) (x : α) :
    foldrM n f x = (List.finRange n).foldrM f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    simp [foldrM_succ, List.finRange_succ, ih, List.foldrM_map]

@[grind =] theorem foldl_eq_finRange_foldl (f : α → Fin n → α) (x : α) :
    foldl n f x = (List.finRange n).foldl f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    simp [foldl_succ, List.finRange_succ, ih, List.foldl_map]

@[grind =] theorem foldr_eq_finRange_foldr (f : Fin n → α → α) (x : α) :
    foldr n f x = (List.finRange n).foldr f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    simp [foldr_succ, List.finRange_succ, ih, List.foldr_map]

end Fin

namespace List

theorem ofFnM_succ {n} [Monad m] [LawfulMonad m] {f : Fin (n + 1) → m α} :
    ofFnM f = (do
      let a ← f 0
      let as ← ofFnM fun i => f i.succ
      pure (a :: as)) := by
  simp [ofFnM, Fin.foldlM_eq_foldlM_finRange, List.finRange_succ, List.foldlM_cons_eq_append,
    List.foldlM_map]

end List
