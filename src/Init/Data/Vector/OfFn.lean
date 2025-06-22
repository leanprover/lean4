/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import all Init.Data.Vector.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Vector.Monadic
import Init.Data.Array.OfFn

/-!
# Theorems about `Vector.ofFn`
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

@[simp, grind =] theorem getElem_ofFn {α n} {f : Fin n → α} (h : i < n) :
    (Vector.ofFn f)[i] = f ⟨i, by simpa using h⟩ := by
  simp [ofFn]

@[simp, grind =] theorem getElem?_ofFn {α n} {f : Fin n → α} :
    (ofFn f)[i]? = if h : i < n then some (f ⟨i, h⟩) else none := by
  simp [getElem?_def]

@[simp 500, grind =]
theorem mem_ofFn {n} {f : Fin n → α} {a : α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  constructor
  · intro w
    obtain ⟨i, h, rfl⟩ := getElem_of_mem w
    exact ⟨⟨i, by simpa using h⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    apply mem_of_getElem (i := i) <;> simp

@[grind =] theorem back_ofFn {n} [NeZero n] {f : Fin n → α} :
    (ofFn f).back = f ⟨n - 1, by have := NeZero.ne n; omega⟩ := by
  simp [back]

theorem ofFn_succ {f : Fin (n+1) → α} :
    ofFn f = (ofFn (fun (i : Fin n) => f i.castSucc)).push (f ⟨n, by omega⟩) := by
  ext i h
  · simp only [getElem_ofFn, getElem_push, Fin.castSucc_mk, left_eq_dite_iff]
    intro h'
    have : i = n := by omega
    simp_all

theorem ofFn_add {n m} {f : Fin (n + m) → α} :
    ofFn f = (ofFn (fun i => f (i.castLE (Nat.le_add_right n m)))) ++ (ofFn (fun i => f (i.natAdd n))) := by
  apply Vector.toArray_inj.mp
  simp [Array.ofFn_add]

theorem ofFn_succ' {f : Fin (n+1) → α} :
    ofFn f = (#v[f 0] ++ ofFn (fun i => f i.succ)).cast (by omega) := by
  apply Vector.toArray_inj.mp
  simp [Array.ofFn_succ']

/-! ### ofFnM -/

/-- Construct (in a monadic context) a vector by applying a monadic function to each index. -/
def ofFnM {n} [Monad m] (f : Fin n → m α) : m (Vector α n) :=
  go 0 (by omega) (Array.emptyWithCapacity n) rfl where
  /-- Auxiliary for `ofFn`. `ofFn.go f i acc = acc ++ #v[f i, ..., f(n - 1)]` -/
  go (i : Nat) (h' : i ≤ n) (acc : Array α) (w : acc.size = i) : m (Vector α n) := do
    if h : i < n then
      go (i+1) (by omega) (acc.push (← f ⟨i, h⟩)) (by simp [w])
    else
      pure ⟨acc, by omega⟩

@[simp, grind =]
theorem ofFnM_zero [Monad m] {f : Fin 0 → m α} : Vector.ofFnM f = pure #v[] := by
  simp [ofFnM, ofFnM.go]

private theorem ofFnM_go_succ {n} [Monad m] [LawfulMonad m] {f : Fin (n + 1) → m α}
    (hi : i ≤ n := by omega) {h : xs.size = i} :
    ofFnM.go f i (by omega) xs h = (do
      let as ← ofFnM.go (fun i => f i.castSucc) i hi xs h
      let a  ← f (Fin.last n)
      pure (as.push a)) := by
  fun_induction ofFnM.go f i (by omega) xs h
  case case1 acc h' h ih =>
    if h : acc.size = n then
      unfold ofFnM.go
      rw [dif_neg (by omega)]
      have h : ¬ acc.size + 1 < n + 1 := by omega
      have : Fin.last n = ⟨acc.size, by omega⟩ := by ext; simp; omega
      simp [*]
    else
      have : acc.size + 1 ≤ n := by omega
      simp only [ih, this]
      conv => rhs; unfold ofFnM.go
      rw [dif_pos (by omega)]
      simp
  case case2 =>
    omega

theorem ofFnM_succ {n} [Monad m] [LawfulMonad m] {f : Fin (n + 1) → m α} :
    ofFnM f = (do
      let as ← ofFnM fun i => f i.castSucc
      let a  ← f (Fin.last n)
      pure (as.push a)) := by
  simp [ofFnM, ofFnM_go_succ]

theorem ofFnM_add {n m} [Monad m] [LawfulMonad m] {f : Fin (n + k) → m α} :
    ofFnM f = (do
      let as ← ofFnM (fun i => f (i.castLE (Nat.le_add_right n k)))
      let bs ← ofFnM (fun i => f (i.natAdd n))
      pure (as ++ bs)) := by
  induction k with
  | zero => simp
  | succ k ih => simp [ofFnM_succ, ih, ← push_append]

@[simp, grind =] theorem toArray_ofFnM [Monad m] [LawfulMonad m] {f : Fin n → m α} :
    toArray <$> ofFnM f = Array.ofFnM f := by
  induction n with
  | zero => simp
  | succ n ih => simp [ofFnM_succ, Array.ofFnM_succ, ← ih]

@[simp, grind =] theorem toList_ofFnM [Monad m] [LawfulMonad m] {f : Fin n → m α} :
    toList <$> Vector.ofFnM f = List.ofFnM f := by
  unfold toList
  suffices Array.toList <$> (toArray <$> ofFnM f) = List.ofFnM f by
    simpa [-toArray_ofFnM]
  simp

theorem ofFnM_succ' {n} [Monad m] [LawfulMonad m] {f : Fin (n + 1) → m α} :
    ofFnM f = (do
      let a ← f 0
      let as ← ofFnM fun i => f i.succ
      pure ((#v[a] ++ as).cast (by omega))) := by
  apply Vector.map_toArray_inj.mp
  simp only [toArray_ofFnM, Array.ofFnM_succ', bind_pure_comp, map_bind, Functor.map_map,
    toArray_cast, toArray_append]
  congr 1
  funext x
  have : (fun xs : Vector α n => #[x] ++ xs.toArray) = (#[x] ++ ·) ∘ toArray := by funext xs; simp
  simp [this, comp_map]

@[simp]
theorem ofFnM_pure_comp [Monad m] [LawfulMonad m] {n} {f : Fin n → α} :
    ofFnM (pure ∘ f) = (pure (ofFn f) : m (Vector α n)) := by
  apply Vector.map_toArray_inj.mp
  simp

-- Variant of `ofFnM_pure_comp` using a lambda.
-- This is not marked a `@[simp]` as it would match on every occurrence of `ofFnM`.
theorem ofFnM_pure [Monad m] [LawfulMonad m] {n} {f : Fin n → α} :
    ofFnM (fun i => pure (f i)) = (pure (ofFn f) : m (Vector α n)) :=
  ofFnM_pure_comp

@[simp, grind =] theorem idRun_ofFnM {f : Fin n → Id α} :
    Id.run (ofFnM f) = ofFn (fun i => Id.run (f i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ofFnM_succ', ofFn_succ', ih]

end Vector
