/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
prelude
import Init.Data.List.Basic
import Init.Data.Fin.Fold

/-!
# Theorems about `List.ofFn`
-/

namespace List

/--
`ofFn f` with `f : fin n → α` returns the list whose ith element is `f i`
```
ofFn f = [f 0, f 1, ... , f (n - 1)]
```
-/
def ofFn {n} (f : Fin n → α) : List α := Fin.foldr n (f · :: ·) []

@[simp]
theorem length_ofFn (f : Fin n → α) : (ofFn f).length = n := by
  simp only [ofFn]
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.foldr_succ, ih]

@[simp]
protected theorem getElem_ofFn (f : Fin n → α) (i : Nat) (h : i < (ofFn f).length) :
    (ofFn f)[i] = f ⟨i, by simp_all⟩ := by
  simp only [ofFn]
  induction n generalizing i with
  | zero => simp at h
  | succ n ih =>
    match i with
    | 0 => simp [Fin.foldr_succ]
    | i+1 =>
      simp only [Fin.foldr_succ]
      apply ih
      simp_all

@[simp]
protected theorem getElem?_ofFn (f : Fin n → α) (i) : (ofFn f)[i]? = if h : i < n then some (f ⟨i, h⟩) else none :=
  if h : i < (ofFn f).length
  then by
    rw [getElem?_eq_getElem h, List.getElem_ofFn]
    · simp only [length_ofFn] at h; simp [h]
  else by
    rw [dif_neg] <;>
    simpa using h

/-- `ofFn` on an empty domain is the empty list. -/
@[simp]
theorem ofFn_zero (f : Fin 0 → α) : ofFn f = [] :=
  ext_get (by simp) (fun i hi₁ hi₂ => by contradiction)

@[simp]
theorem ofFn_succ {n} (f : Fin (n + 1) → α) : ofFn f = f 0 :: ofFn fun i => f i.succ :=
  ext_get (by simp) (fun i hi₁ hi₂ => by
    cases i
    · simp
    · simp)

@[simp]
theorem ofFn_eq_nil_iff {f : Fin n → α} : ofFn f = [] ↔ n = 0 := by
  cases n <;> simp only [ofFn_zero, ofFn_succ, eq_self_iff_true, Nat.succ_ne_zero, reduceCtorEq]

theorem head_ofFn {n} (f : Fin n → α) (h : ofFn f ≠ []) :
    (ofFn f).head h = f ⟨0, Nat.pos_of_ne_zero (mt ofFn_eq_nil_iff.2 h)⟩ := by
  rw [← getElem_zero (length_ofFn _ ▸ Nat.pos_of_ne_zero (mt ofFn_eq_nil_iff.2 h)),
    List.getElem_ofFn]

theorem getLast_ofFn {n} (f : Fin n → α) (h : ofFn f ≠ []) :
    (ofFn f).getLast h = f ⟨n - 1, Nat.sub_one_lt (mt ofFn_eq_nil_iff.2 h)⟩ := by
  simp [getLast_eq_getElem, length_ofFn, List.getElem_ofFn]

end List
