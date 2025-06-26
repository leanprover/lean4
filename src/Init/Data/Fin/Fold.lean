/-
Copyright (c) 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

prelude
import Init.Data.Nat.Linear
import Init.Control.Lawful.Basic
import Init.Data.Fin.Lemmas

namespace Fin

/--
Combine all the values that can be represented by `Fin n` with an initial value, starting at `0` and
nesting to the left.

Example:
 * `Fin.foldl 3 (· + ·.val) (0 : Nat) = ((0 + (0 : Fin 3).val) + (1 : Fin 3).val) + (2 : Fin 3).val`
-/
@[inline] def foldl (n) (f : α → Fin n → α) (init : α) : α := loop init 0 where
  /-- Inner loop for `Fin.foldl`. `Fin.foldl.loop n f x i = f (f (f x i) ...) (n-1)`  -/
  @[semireducible, specialize] loop (x : α) (i : Nat) : α :=
    if h : i < n then loop (f x ⟨i, h⟩) (i+1) else x
  termination_by n - i

/--
Combine all the values that can be represented by `Fin n` with an initial value, starting at `n - 1`
and nesting to the right.

Example:
 * `Fin.foldr 3 (·.val + ·) (0 : Nat) = (0 : Fin 3).val + ((1 : Fin 3).val + ((2 : Fin 3).val + 0))`
-/
@[inline] def foldr (n) (f : Fin n → α → α) (init : α) : α := loop n (Nat.le_refl n) init where
  /-- Inner loop for `Fin.foldr`. `Fin.foldr.loop n f i x = f 0 (f ... (f (i-1) x))`  -/
  @[specialize] loop : (i : _) → i ≤ n → α → α
  | 0, _, x => x
  | i+1, h, x => loop i (Nat.le_of_lt h) (f ⟨i, h⟩ x)
  termination_by structural i => i

/--
Folds a monadic function over all the values in `Fin n` from left to right, starting with `0`.

It is the sequence of steps:
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
Folds a monadic function over `Fin n` from right to left, starting with `n-1`.

It is the sequence of steps:
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

@[congr] theorem foldlM_congr [Monad m] {n k : Nat} (w : n = k) (f : α → Fin n → m α) :
    foldlM n f = foldlM k (fun x i => f x (i.cast w.symm)) := by
  subst w
  rfl

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

@[simp] theorem foldlM_zero [Monad m] (f : α → Fin 0 → m α) : foldlM 0 f = pure := by
  funext x
  exact foldlM_loop_eq ..

theorem foldlM_succ [Monad m] (f : α → Fin (n+1) → m α) :
    foldlM (n+1) f = fun x => f x 0 >>= foldlM n (fun x j => f x j.succ) := by
  funext x
  exact foldlM_loop ..

/-- Variant of `foldlM_succ` that splits off `Fin.last n` rather than `0`. -/
theorem foldlM_succ_last [Monad m] [LawfulMonad m] (f : α → Fin (n+1) → m α) :
    foldlM (n+1) f = fun x => foldlM n (fun x j => f x j.castSucc) x >>= (f · (Fin.last n)) := by
  funext x
  induction n generalizing x with
  | zero =>
    simp [foldlM_succ]
  | succ n ih =>
    rw [foldlM_succ]
    conv => rhs; rw [foldlM_succ]
    simp only [castSucc_zero, castSucc_succ, bind_assoc]
    congr 1
    funext x
    rw [ih]
    simp

theorem foldlM_add [Monad m] [LawfulMonad m] (f : α → Fin (n + k) → m α) :
    foldlM (n + k) f =
      fun x => foldlM n (fun x i => f x (i.castLE (Nat.le_add_right n k))) x >>= foldlM k (fun x i => f x (i.natAdd n)) := by
  induction k with
  | zero =>
    funext x
    simp
  | succ k ih =>
    funext x
    simp [foldlM_succ_last, ← Nat.add_assoc, ih]

/-! ### foldrM -/

@[congr] theorem foldrM_congr [Monad m] {n k : Nat} (w : n = k) (f : Fin n → α → m α) :
    foldrM n f = foldrM k (fun i => f (i.cast w.symm)) := by
  subst w
  rfl

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
    rfl
  | succ i ih =>
    rw [foldrM_loop_succ, foldrM_loop_succ, bind_assoc]
    congr; funext; exact ih ..

@[simp] theorem foldrM_zero [Monad m] (f : Fin 0 → α → m α) : foldrM 0 f = pure := by
  funext x
  exact foldrM_loop_zero ..

theorem foldrM_succ [Monad m] [LawfulMonad m] (f : Fin (n+1) → α → m α) :
    foldrM (n+1) f = fun x => foldrM n (fun i => f i.succ) x >>= f 0 := by
  funext x
  exact foldrM_loop ..

theorem foldrM_succ_last [Monad m] [LawfulMonad m] (f : Fin (n+1) → α → m α) :
    foldrM (n+1) f = fun x => f (Fin.last n) x >>= foldrM n (fun i => f i.castSucc) := by
  funext x
  induction n generalizing x with
  | zero => simp [foldrM_succ]
  | succ n ih =>
    rw [foldrM_succ]
    conv => rhs; rw [foldrM_succ]
    simp [ih]

theorem foldrM_add [Monad m] [LawfulMonad m] (f : Fin (n + k) → α → m α) :
    foldrM (n + k) f =
      fun x => foldrM k (fun i => f (i.natAdd n)) x >>= foldrM n (fun i => f (i.castLE (Nat.le_add_right n k))) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    funext x
    simp [foldrM_succ_last, ← Nat.add_assoc, ih]

/-! ### foldl -/

@[congr] theorem foldl_congr {n k : Nat} (w : n = k) (f : α → Fin n → α) :
    foldl n f = foldl k (fun x i => f x (i.cast w.symm)) := by
  subst w
  rfl

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
  | zero => simp [Fin.last]
  | succ n ih => rw [foldl_succ, ih (f · ·.succ), foldl_succ]; simp

theorem foldl_add (f : α → Fin (n + m) → α) (x) :
    foldl (n + m) f x =
      foldl m (fun x i => f x (i.natAdd n))
        (foldl n (fun x i => f x (i.castLE (Nat.le_add_right n m))) x):= by
  induction m with
  | zero => simp
  | succ m ih => simp [foldl_succ_last, ih, ← Nat.add_assoc]

theorem foldl_eq_foldlM (f : α → Fin n → α) (x) :
    foldl n f x = (foldlM (m := Id) n (pure <| f · ·) x).run := by
  induction n generalizing x <;> simp [foldl_succ, foldlM_succ, *]

-- This is not marked `@[simp]` as it would match on every occurrence of `foldlM`.
theorem foldlM_pure [Monad m] [LawfulMonad m] {n} {f : α → Fin n → α} :
    foldlM n (fun x i => pure (f x i)) x = (pure (foldl n f x) : m α) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [foldlM_succ, foldl_succ, ih]

/-! ### foldr -/

@[congr] theorem foldr_congr {n k : Nat} (w : n = k) (f : Fin n → α → α) :
    foldr n f = foldr k (fun i => f (i.cast w.symm)) := by
  subst w
  rfl

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
  | succ n ih => rw [foldr_succ, ih (f ·.succ), foldr_succ]; simp

theorem foldr_add (f : Fin (n + m) → α → α) (x) :
    foldr (n + m) f x =
      foldr n (fun i => f (i.castLE (Nat.le_add_right n m)))
        (foldr m (fun i => f (i.natAdd n)) x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => simp [foldr_succ_last, ih, ← Nat.add_assoc]

theorem foldr_eq_foldrM (f : Fin n → α → α) (x) :
    foldr n f x = (foldrM (m := Id) n (pure <| f · ·) x).run := by
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

-- This is not marked `@[simp]` as it would match on every occurrence of `foldrM`.
theorem foldrM_pure [Monad m] [LawfulMonad m] {n} {f : Fin n → α → α} :
    foldrM n (fun i x => pure (f i x)) x = (pure (foldr n f x) : m α) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [foldrM_succ, foldr_succ, ih]

end Fin
