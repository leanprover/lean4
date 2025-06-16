/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import all Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Init.Data.Array.Monadic
import Init.Data.List.OfFn
import Init.Data.List.FinRange

/-!
# Theorems about `Array.ofFn`
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

/-! ### ofFn -/

@[simp, grind =] theorem ofFn_zero {f : Fin 0 → α} : ofFn f = #[] := by
  simp [ofFn, ofFn.go]

theorem ofFn_succ {f : Fin (n+1) → α} :
    ofFn f = (ofFn (fun (i : Fin n) => f i.castSucc)).push (f ⟨n, by omega⟩) := by
  ext i h₁ h₂
  · simp
  · simp only [getElem_ofFn, getElem_push, size_ofFn, Fin.castSucc_mk, left_eq_dite_iff,
      Nat.not_lt]
    simp only [size_ofFn] at h₁
    intro h₃
    simp only [show i = n by omega]

theorem ofFn_add {n m} {f : Fin (n + m) → α} :
    ofFn f = (ofFn (fun i => f (i.castLE (Nat.le_add_right n m)))) ++ (ofFn (fun i => f (i.natAdd n))) := by
  induction m with
  | zero => simp
  | succ m ih => simp [ofFn_succ, ih]

@[simp, grind =] theorem _root_.List.toArray_ofFn {f : Fin n → α} : (List.ofFn f).toArray = Array.ofFn f := by
  ext <;> simp

@[simp, grind =] theorem toList_ofFn {f : Fin n → α} : (Array.ofFn f).toList = List.ofFn f := by
  apply List.ext_getElem <;> simp

theorem ofFn_succ' {f : Fin (n+1) → α} :
    ofFn f = #[f 0] ++ ofFn (fun i => f i.succ) := by
  apply Array.toList_inj.mp
  simp [List.ofFn_succ]

@[simp]
theorem ofFn_eq_empty_iff {f : Fin n → α} : ofFn f = #[] ↔ n = 0 := by
  rw [← Array.toList_inj]
  simp

@[simp 500, grind =]
theorem mem_ofFn {n} {f : Fin n → α} {a : α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  constructor
  · intro w
    obtain ⟨i, h, rfl⟩ := getElem_of_mem w
    exact ⟨⟨i, by simpa using h⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    apply mem_of_getElem (i := i) <;> simp

/-! ### ofFnM -/

/-- Construct (in a monadic context) an array by applying a monadic function to each index. -/
def ofFnM {n} [Monad m] (f : Fin n → m α) : m (Array α) :=
  Fin.foldlM n (fun xs i => xs.push <$> f i) (Array.emptyWithCapacity n)

@[simp, grind =]
theorem ofFnM_zero [Monad m] {f : Fin 0 → m α} : ofFnM f = pure #[] := by
  simp [ofFnM]

theorem ofFnM_succ' {n} [Monad m] [LawfulMonad m] {f : Fin (n + 1) → m α} :
    ofFnM f = (do
      let a ← f 0
      let as ← ofFnM fun i => f i.succ
      pure (#[a] ++ as)) := by
  simp [ofFnM, Fin.foldlM_eq_foldlM_finRange, List.foldlM_push_eq_append, List.finRange_succ, Function.comp_def]

theorem ofFnM_succ {n} [Monad m] [LawfulMonad m] {f : Fin (n + 1) → m α} :
    ofFnM f = (do
      let as ← ofFnM fun i => f i.castSucc
      let a  ← f (Fin.last n)
      pure (as.push a)) := by
  simp [ofFnM, Fin.foldlM_succ_last]

theorem ofFnM_add {n m} [Monad m] [LawfulMonad m] {f : Fin (n + k) → m α} :
    ofFnM f = (do
      let as ← ofFnM fun i : Fin n => f (i.castLE (Nat.le_add_right n k))
      let bs ← ofFnM fun i : Fin k => f (i.natAdd n)
      pure (as ++ bs)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [ofFnM_succ, Nat.add_eq, ih, Fin.castSucc_castLE, Fin.castSucc_natAdd, bind_pure_comp,
      bind_assoc, bind_map_left, Fin.natAdd_last, map_bind, Functor.map_map]
    congr 1
    funext xs
    congr 1
    funext ys
    congr 1
    funext x
    simp

@[simp, grind =] theorem toList_ofFnM [Monad m] [LawfulMonad m] {f : Fin n → m α} :
    toList <$> ofFnM f = List.ofFnM f := by
  induction n with
  | zero => simp
  | succ n ih => simp [ofFnM_succ, List.ofFnM_succ_last, ← ih]

@[simp]
theorem ofFnM_pure_comp [Monad m] [LawfulMonad m] {n} {f : Fin n → α} :
    ofFnM (pure ∘ f) = (pure (ofFn f) : m (Array α)) := by
  apply Array.map_toList_inj.mp
  simp

-- Variant of `ofFnM_pure_comp` using a lambda.
-- This is not marked a `@[simp]` as it would match on every occurrence of `ofFnM`.
theorem ofFnM_pure [Monad m] [LawfulMonad m] {n} {f : Fin n → α} :
    ofFnM (fun i => pure (f i)) = (pure (ofFn f) : m (Array α)) :=
  ofFnM_pure_comp

@[simp, grind =] theorem idRun_ofFnM {f : Fin n → Id α} :
    Id.run (ofFnM f) = ofFn (fun i => Id.run (f i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ofFnM_succ', ofFn_succ', ih]

end Array
