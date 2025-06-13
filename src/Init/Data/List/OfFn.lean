/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
module

prelude
import Init.Data.List.Basic
import Init.Data.Fin.Fold

/-!
# Theorems about `List.ofFn`
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/--
Creates a list by applying `f` to each potential index in order, starting at `0`.

Examples:
 * `List.ofFn (n := 3) toString = ["0", "1", "2"]`
 * `List.ofFn (fun i => #["red", "green", "blue"].get i.val i.isLt) = ["red", "green", "blue"]`
-/
def ofFn {n} (f : Fin n → α) : List α := Fin.foldr n (f · :: ·) []

/--
Creates a list wrapped in a monad by applying the monadic function `f : Fin n → m α`
to each potential index in order, starting at `0`.
-/
def ofFnM {n} [Monad m] (f : Fin n → m α) : m (List α) :=
  List.reverse <$> Fin.foldlM n (fun xs i => (· :: xs) <$> f i) []

@[simp, grind =]
theorem length_ofFn {f : Fin n → α} : (ofFn f).length = n := by
  simp only [ofFn]
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.foldr_succ, ih]

@[simp, grind =]
protected theorem getElem_ofFn {f : Fin n → α} (h : i < (ofFn f).length) :
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

@[simp, grind =]
protected theorem getElem?_ofFn {f : Fin n → α} :
    (ofFn f)[i]? = if h : i < n then some (f ⟨i, h⟩) else none :=
  if h : i < (ofFn f).length
  then by
    rw [getElem?_eq_getElem h, List.getElem_ofFn]
    · simp only [length_ofFn] at h; simp [h]
  else by
    rw [dif_neg] <;>
    simpa using h

/-- `ofFn` on an empty domain is the empty list. -/
@[simp, grind =]
theorem ofFn_zero {f : Fin 0 → α} : ofFn f = [] := by
  rw [ofFn, Fin.foldr_zero]

@[simp]
theorem ofFn_succ {n} {f : Fin (n + 1) → α} : ofFn f = f 0 :: ofFn fun i => f i.succ :=
  ext_get (by simp) (fun i hi₁ hi₂ => by
    cases i
    · simp
    · simp)

theorem ofFn_succ_last {n} {f : Fin (n + 1) → α} :
    ofFn f = (ofFn fun i => f i.castSucc) ++ [f (Fin.last n)] := by
  induction n with
  | zero => simp [ofFn_succ]
  | succ n ih =>
    rw [ofFn_succ]
    conv => rhs; rw [ofFn_succ]
    rw [ih]
    simp

theorem ofFn_add {n m} {f : Fin (n + m) → α} :
    ofFn f = (ofFn fun i => f (i.castLE (Nat.le_add_right n m))) ++ (ofFn fun i => f (i.natAdd n)) := by
  induction m with
  | zero => simp
  | succ m ih => simp [-ofFn_succ, ofFn_succ_last, ih]

@[simp]
theorem ofFn_eq_nil_iff {f : Fin n → α} : ofFn f = [] ↔ n = 0 := by
  cases n <;> simp only [ofFn_zero, ofFn_succ, eq_self_iff_true, Nat.succ_ne_zero, reduceCtorEq]

@[simp 500, grind =]
theorem mem_ofFn {n} {f : Fin n → α} {a : α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  constructor
  · intro w
    obtain ⟨i, h, rfl⟩ := getElem_of_mem w
    exact ⟨⟨i, by simpa using h⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    apply mem_of_getElem (i := i) <;> simp

@[grind =] theorem head_ofFn {n} {f : Fin n → α} (h : ofFn f ≠ []) :
    (ofFn f).head h = f ⟨0, Nat.pos_of_ne_zero (mt ofFn_eq_nil_iff.2 h)⟩ := by
  rw [← getElem_zero (length_ofFn ▸ Nat.pos_of_ne_zero (mt ofFn_eq_nil_iff.2 h)),
    List.getElem_ofFn]

@[grind =]theorem getLast_ofFn {n} {f : Fin n → α} (h : ofFn f ≠ []) :
    (ofFn f).getLast h = f ⟨n - 1, Nat.sub_one_lt (mt ofFn_eq_nil_iff.2 h)⟩ := by
  simp [getLast_eq_getElem, length_ofFn, List.getElem_ofFn]

/-- `ofFnM` on an empty domain is the empty list. -/
@[simp, grind =]
theorem ofFnM_zero [Monad m] [LawfulMonad m] {f : Fin 0 → m α} : ofFnM f = pure [] := by
  simp [ofFnM]

/-! See `Init.Data.List.FinRange` for the `ofFnM_succ` variant. -/

theorem ofFnM_succ_last {n} [Monad m] [LawfulMonad m] {f : Fin (n + 1) → m α} :
    ofFnM f = (do
      let as ← ofFnM fun i => f i.castSucc
      let a  ← f (Fin.last n)
      pure (as ++ [a])) := by
  simp [ofFnM, Fin.foldlM_succ_last]

theorem ofFnM_add {n m} [Monad m] [LawfulMonad m] {f : Fin (n + k) → m α} :
    ofFnM f = (do
      let as ← ofFnM fun i : Fin n => f (i.castLE (Nat.le_add_right n k))
      let bs ← ofFnM fun i : Fin k => f (i.natAdd n)
      pure (as ++ bs)) := by
  induction k with
  | zero => simp
  | succ k ih => simp [ofFnM_succ_last, ih]


end List

namespace Fin

theorem foldl_cons_eq_append {f : Fin n → α} {xs : List α} :
    Fin.foldl n (fun xs i => f i :: xs) xs = (List.ofFn f).reverse ++ xs := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih => simp [Fin.foldl_succ, List.ofFn_succ, ih]

theorem foldr_cons_eq_append {f : Fin n → α} {xs : List α} :
    Fin.foldr n (fun i xs => f i :: xs) xs = List.ofFn f ++ xs:= by
  induction n generalizing xs with
  | zero => simp
  | succ n ih => simp [Fin.foldr_succ, List.ofFn_succ, ih]

end Fin

namespace List

@[simp]
theorem ofFnM_pure_comp [Monad m] [LawfulMonad m] {n} {f : Fin n → α} :
    ofFnM (pure ∘ f) = (pure (ofFn f) : m (List α)) := by
  simp [ofFnM, Fin.foldlM_pure, Fin.foldl_cons_eq_append]

-- Variant of `ofFnM_pure_comp` using a lambda.
-- This is not marked a `@[simp]` as it would match on every occurrence of `ofFnM`.
theorem ofFnM_pure [Monad m] [LawfulMonad m] {n} {f : Fin n → α} :
    ofFnM (fun i => pure (f i)) = (pure (ofFn f) : m (List α)) :=
  ofFnM_pure_comp

@[simp, grind =] theorem idRun_ofFnM {f : Fin n → Id α} :
    Id.run (ofFnM f) = ofFn (fun i => Id.run (f i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [-ofFn_succ, ofFnM_succ_last, ofFn_succ_last, ih]

end List
