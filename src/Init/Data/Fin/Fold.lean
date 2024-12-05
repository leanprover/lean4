/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
prelude
import Init.Data.Nat.Linear
import Init.Control.Lawful.Basic
import Init.Data.Fin.Lemmas

namespace Fin

/-- Folds over `Fin n` from the left: `foldl 3 f x = f (f (f x 0) 1) 2`. -/
@[inline] def foldl (n) (f : α → Fin n → α) (init : α) : α := loop init 0 where
  /-- Inner loop for `Fin.foldl`. `Fin.foldl.loop n f x i = f (f (f x i) ...) (n-1)`  -/
  @[semireducible, specialize] loop (x : α) (i : Nat) : α :=
    if h : i < n then loop (f x ⟨i, h⟩) (i+1) else x
  termination_by n - i

/-- Folds over `Fin n` from the right: `foldr 3 f x = f 0 (f 1 (f 2 x))`. -/
@[inline] def foldr (n) (f : Fin n → α → α) (init : α) : α := loop n (Nat.le_refl n) init where
  /-- Inner loop for `Fin.foldr`. `Fin.foldr.loop n f i x = f 0 (f ... (f (i-1) x))`  -/
  @[specialize] loop : (i : _) → i ≤ n → α → α
  | 0, _, x => x
  | i+1, h, x => loop i (Nat.le_of_lt h) (f ⟨i, h⟩ x)
  termination_by structural i => i

/--
Folds a monadic function over `Fin n` from left to right:
```
Fin.foldlM n f x₀ = do
  let x₁ ← f x₀ 0
  let x₂ ← f x₁ 1
  ...
  let xₙ ← f xₙ₋₁ (n-1)
  pure xₙ
```
-/
@[inline] def foldlM [Monad m] (n) (f : α → Fin n → m α) (init : α) : m α := loop init 0 where
  /--
  Inner loop for `Fin.foldlM`.
  ```
  Fin.foldlM.loop n f xᵢ i = do
    let xᵢ₊₁ ← f xᵢ i
    ...
    let xₙ ← f xₙ₋₁ (n-1)
    pure xₙ
  ```
  -/
  @[semireducible, specialize] loop (x : α) (i : Nat) : m α := do
    if h : i < n then f x ⟨i, h⟩ >>= (loop · (i+1)) else pure x
  termination_by n - i
  decreasing_by decreasing_trivial_pre_omega

/--
Folds a monadic function over `Fin n` from right to left:
```
Fin.foldrM n f xₙ = do
  let xₙ₋₁ ← f (n-1) xₙ
  let xₙ₋₂ ← f (n-2) xₙ₋₁
  ...
  let x₀ ← f 0 x₁
  pure x₀
```
-/
@[inline] def foldrM [Monad m] (n) (f : Fin n → α → m α) (init : α) : m α :=
  loop ⟨n, Nat.le_refl n⟩ init where
  /--
  Inner loop for `Fin.foldrM`.
  ```
  Fin.foldrM.loop n f i xᵢ = do
    let xᵢ₋₁ ← f (i-1) xᵢ
    ...
    let x₁ ← f 1 x₂
    let x₀ ← f 0 x₁
    pure x₀
  ```
  -/
  @[semireducible, specialize] loop : {i // i ≤ n} → α → m α
  | ⟨0, _⟩, x => pure x
  | ⟨i+1, h⟩, x => f ⟨i, h⟩ x >>= loop ⟨i, Nat.le_of_lt h⟩

/-! ### foldlM -/

theorem foldlM_loop_lt [Monad m] (f : α → Fin n → m α) (x) (h : i < n) :
    foldlM.loop n f x i = f x ⟨i, h⟩ >>= (foldlM.loop n f . (i+1)) := by
  rw [foldlM.loop, dif_pos h]

theorem foldlM_loop_eq [Monad m] (f : α → Fin n → m α) (x) : foldlM.loop n f x n = pure x := by
  rw [foldlM.loop, dif_neg (Nat.lt_irrefl _)]

theorem foldlM_loop [Monad m] (f : α → Fin (n+1) → m α) (x) (h : i < n+1) :
    foldlM.loop (n+1) f x i = f x ⟨i, h⟩ >>= (foldlM.loop n (fun x j => f x j.succ) . i) := by
  if h' : i < n then
    rw [foldlM_loop_lt _ _ h]
    congr; funext
    rw [foldlM_loop_lt _ _ h', foldlM_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [foldlM_loop_lt]
    congr; funext
    rw [foldlM_loop_eq, foldlM_loop_eq]
termination_by n - i

@[simp] theorem foldlM_zero [Monad m] (f : α → Fin 0 → m α) (x) : foldlM 0 f x = pure x :=
  foldlM_loop_eq ..

theorem foldlM_succ [Monad m] (f : α → Fin (n+1) → m α) (x) :
    foldlM (n+1) f x = f x 0 >>= foldlM n (fun x j => f x j.succ) := foldlM_loop ..

/-! ### foldrM -/

theorem foldrM_loop_zero [Monad m] (f : Fin n → α → m α) (x) :
    foldrM.loop n f ⟨0, Nat.zero_le _⟩ x = pure x := by
  rw [foldrM.loop]

theorem foldrM_loop_succ [Monad m] (f : Fin n → α → m α) (x) (h : i < n) :
    foldrM.loop n f ⟨i+1, h⟩ x = f ⟨i, h⟩ x >>= foldrM.loop n f ⟨i, Nat.le_of_lt h⟩ := by
  rw [foldrM.loop]

theorem foldrM_loop [Monad m] [LawfulMonad m] (f : Fin (n+1) → α → m α) (x) (h : i+1 ≤ n+1) :
    foldrM.loop (n+1) f ⟨i+1, h⟩ x =
      foldrM.loop n (fun j => f j.succ) ⟨i, Nat.le_of_succ_le_succ h⟩ x >>= f 0 := by
  induction i generalizing x with
  | zero =>
    rw [foldrM_loop_zero, foldrM_loop_succ, pure_bind]
    conv => rhs; rw [←bind_pure (f 0 x)]
    congr; funext
  | succ i ih =>
    rw [foldrM_loop_succ, foldrM_loop_succ, bind_assoc]
    congr; funext; exact ih ..

@[simp] theorem foldrM_zero [Monad m] (f : Fin 0 → α → m α) (x) : foldrM 0 f x = pure x :=
  foldrM_loop_zero ..

theorem foldrM_succ [Monad m] [LawfulMonad m] (f : Fin (n+1) → α → m α) (x) :
    foldrM (n+1) f x = foldrM n (fun i => f i.succ) x >>= f 0 := foldrM_loop ..

/-! ### foldl -/

theorem foldl_loop_lt (f : α → Fin n → α) (x) (h : i < n) :
    foldl.loop n f x i = foldl.loop n f (f x ⟨i, h⟩) (i+1) := by
  rw [foldl.loop, dif_pos h]

theorem foldl_loop_eq (f : α → Fin n → α) (x) : foldl.loop n f x n = x := by
  rw [foldl.loop, dif_neg (Nat.lt_irrefl _)]

theorem foldl_loop (f : α → Fin (n+1) → α) (x) (h : i < n+1) :
    foldl.loop (n+1) f x i = foldl.loop n (fun x j => f x j.succ) (f x ⟨i, h⟩) i := by
  if h' : i < n then
    rw [foldl_loop_lt _ _ h]
    rw [foldl_loop_lt _ _ h', foldl_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [foldl_loop_lt]
    rw [foldl_loop_eq, foldl_loop_eq]

@[simp] theorem foldl_zero (f : α → Fin 0 → α) (x) : foldl 0 f x = x :=
  foldl_loop_eq ..

theorem foldl_succ (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = foldl n (fun x i => f x i.succ) (f x 0) :=
  foldl_loop ..

theorem foldl_succ_last (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = f (foldl n (f · ·.castSucc) x) (last n) := by
  rw [foldl_succ]
  induction n generalizing x with
  | zero => simp [foldl_succ, Fin.last]
  | succ n ih => rw [foldl_succ, ih (f · ·.succ), foldl_succ]; simp [succ_castSucc]

theorem foldl_eq_foldlM (f : α → Fin n → α) (x) :
    foldl n f x = foldlM (m:=Id) n f x := by
  induction n generalizing x <;> simp [foldl_succ, foldlM_succ, *]

/-! ### foldr -/

theorem foldr_loop_zero (f : Fin n → α → α) (x) :
    foldr.loop n f 0 (Nat.zero_le _) x = x := by
  rw [foldr.loop]

theorem foldr_loop_succ (f : Fin n → α → α) (x) (h : i < n) :
    foldr.loop n f (i+1) h x = foldr.loop n f i (Nat.le_of_lt h) (f ⟨i, h⟩ x) := by
  rw [foldr.loop]

theorem foldr_loop (f : Fin (n+1) → α → α) (x) (h : i+1 ≤ n+1) :
    foldr.loop (n+1) f (i+1) h x =
      f 0 (foldr.loop n (fun j => f j.succ) i (Nat.le_of_succ_le_succ h) x) := by
  induction i generalizing x with
  | zero => simp [foldr_loop_succ, foldr_loop_zero]
  | succ i ih => rw [foldr_loop_succ, ih]; rfl

@[simp] theorem foldr_zero (f : Fin 0 → α → α) (x) : foldr 0 f x = x :=
  foldr_loop_zero ..

theorem foldr_succ (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = f 0 (foldr n (fun i => f i.succ) x) := foldr_loop ..

theorem foldr_succ_last (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = foldr n (f ·.castSucc) (f (last n) x) := by
  induction n generalizing x with
  | zero => simp [foldr_succ, Fin.last]
  | succ n ih => rw [foldr_succ, ih (f ·.succ), foldr_succ]; simp [succ_castSucc]

theorem foldr_eq_foldrM (f : Fin n → α → α) (x) :
    foldr n f x = foldrM (m:=Id) n f x := by
  induction n <;> simp [foldr_succ, foldrM_succ, *]

theorem foldl_rev (f : Fin n → α → α) (x) :
    foldl n (fun x i => f i.rev x) x = foldr n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [foldl_succ, foldr_succ_last, ← ih]; simp [rev_succ]

theorem foldr_rev (f : α → Fin n → α) (x) :
     foldr n (fun i x => f x i.rev) x = foldl n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [foldl_succ_last, foldr_succ, ← ih]; simp [rev_succ]

end Fin
