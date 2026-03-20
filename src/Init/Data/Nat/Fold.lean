/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Kim Morrison
-/
module

prelude
public import Init.Data.List.FinRange
import Init.Data.Fin.Lemmas
import Init.Data.List.Lemmas
import Init.Omega

public section

set_option linter.missingDocs true -- keep it documented
universe u

namespace Nat

/--
Iterates the application of a function `f` to a starting value `init`, `n` times. At each step, `f`
is applied to the current value and to the next natural number less than `n`, in increasing order.

Examples:
* `Nat.fold 3 f init = (init |> f 0 (by simp) |> f 1 (by simp) |> f 2 (by simp))`
* `Nat.fold 4 (fun i _ xs => xs.push i) #[] = #[0, 1, 2, 3]`
* `Nat.fold 0 (fun i _ xs => xs.push i) #[] = #[]`
-/
@[specialize] def fold {α : Type u} : (n : Nat) → (f : (i : Nat) → i < n → α → α) → (init : α) → α
  | 0,      f, a => a
  | succ n, f, a => f n (by omega) (fold n (fun i h => f i (by omega)) a)


/--
Iterates the application of a function `f` to a starting value `init`, `n` times. At each step, `f`
is applied to the current value and to the next natural number less than `n`, in increasing order.

This is a tail-recursive version of `Nat.fold` that's used at runtime.

Examples:
* `Nat.foldTR 3 f init = (init |> f 0 (by simp) |> f 1 (by simp) |> f 2 (by simp))`
* `Nat.foldTR 4 (fun i _ xs => xs.push i) #[] = #[0, 1, 2, 3]`
* `Nat.foldTR 0 (fun i _ xs => xs.push i) #[] = #[]`
-/
@[inline] def foldTR {α : Type u} (n : Nat) (f : (i : Nat) → i < n → α → α) (init : α) : α :=
  let rec @[specialize] loop : ∀ j, j ≤ n → α → α
    | 0,      h, a => a
    | succ m, h, a => loop m (by omega) (f (n - succ m) (by omega) a)
  loop n (by omega) init

/--
Iterates the application of a function `f` to a starting value `init`, `n` times. At each step, `f`
is applied to the current value and to the next natural number less than `n`, in decreasing order.

Examples:
* `Nat.foldRev 3 f init = (f 0 (by simp) <| f 1 (by simp) <| f 2 (by simp) init)`
* `Nat.foldRev 4 (fun i _ xs => xs.push i) #[] = #[3, 2, 1, 0]`
* `Nat.foldRev 0 (fun i _ xs => xs.push i) #[] = #[]`
-/
@[specialize] def foldRev {α : Type u} : (n : Nat) → (f : (i : Nat) → i < n → α → α) → (init : α) → α
  | 0,      f, a => a
  | succ n, f, a => foldRev n (fun i h => f i (by omega)) (f n (by omega) a)

/--
Checks whether there is some number less that the given bound for which `f` returns `true`.

Examples:
 * `Nat.any 4 (fun i _ => i < 5) = true`
 * `Nat.any 7 (fun i _ => i < 5) = true`
 * `Nat.any 7 (fun i _ => i % 2 = 0) = true`
 * `Nat.any 1 (fun i _ => i % 2 = 1) = false`
-/
@[specialize] def any : (n : Nat) → (f : (i : Nat) → i < n → Bool) → Bool
  | 0,      f => false
  | succ n, f => any n (fun i h => f i (by omega)) || f n (by omega)

/--
Checks whether there is some number less that the given bound for which `f` returns `true`.

This is a tail-recursive equivalent of `Nat.any` that's used at runtime.

Examples:
 * `Nat.anyTR 4 (fun i _ => i < 5) = true`
 * `Nat.anyTR 7 (fun i _ => i < 5) = true`
 * `Nat.anyTR 7 (fun i _ => i % 2 = 0) = true`
 * `Nat.anyTR 1 (fun i _ => i % 2 = 1) = false`
-/
@[inline] def anyTR (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  let rec @[specialize] loop : (i : Nat) → i ≤ n → Bool
    | 0,      h => false
    | succ m, h => f (n - succ m) (by omega) || loop m (by omega)
  loop n (by omega)

/--
Checks whether `f` returns `true` for every number strictly less than a bound.

Examples:
 * `Nat.all 4 (fun i _ => i < 5) = true`
 * `Nat.all 7 (fun i _ => i < 5) = false`
 * `Nat.all 7 (fun i _ => i % 2 = 0) = false`
 * `Nat.all 1 (fun i _ => i % 2 = 0) = true`
-/
@[specialize] def all : (n : Nat) → (f : (i : Nat) → i < n → Bool) → Bool
  | 0,      f => true
  | succ n, f => all n (fun i h => f i (by omega)) && f n (by omega)

/--
Checks whether `f` returns `true` for every number strictly less than a bound.

This is a tail-recursive equivalent of `Nat.all` that's used at runtime.

Examples:
 * `Nat.allTR 4 (fun i _ => i < 5) = true`
 * `Nat.allTR 7 (fun i _ => i < 5) = false`
 * `Nat.allTR 7 (fun i _ => i % 2 = 0) = false`
 * `Nat.allTR 1 (fun i _ => i % 2 = 0) = true`
-/
@[inline] def allTR (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  let rec @[specialize] loop : (i : Nat) → i ≤ n   → Bool
    | 0,      h => true
    | succ m, h => f (n - succ m) (by omega) && loop m (by omega)
  loop n (by omega)

/-! # csimp theorems -/

theorem fold_congr {α : Type u} {n m : Nat} (w : n = m)
     (f : (i : Nat) → i < n → α → α) (init : α) :
     fold n f init = fold m (fun i h => f i (by omega)) init := by
  subst m
  rfl

theorem foldRev_congr {α : Type u} {n m : Nat} (w : n = m)
     (f : (i : Nat) → i < n → α → α) (init : α) :
     foldRev n f init = foldRev m (fun i h => f i (by omega)) init := by
  subst m
  rfl

private theorem foldTR_loop_congr {α : Type u} {n m : Nat} (w : n = m)
     (f : (i : Nat) → i < n → α → α) (j : Nat) (h : j ≤ n) (init : α) :
     foldTR.loop n f j h init = foldTR.loop m (fun i h => f i (by omega)) j (by omega) init := by
  subst m
  rfl

@[csimp] theorem fold_eq_foldTR : @fold = @foldTR :=
  funext fun α => funext fun n => funext fun f => funext fun init =>
  let rec go : ∀ m n f, fold (m + n) f init = foldTR.loop (m + n) f m (by omega) (fold n (fun i h => f i (by omega)) init)
    | 0,      n, f => by
      simp only [foldTR.loop]
      have t : 0 + n = n := by omega
      rw [fold_congr t]
    | succ m, n, f => by
      have t : (m + 1) + n = m + (n + 1) := by omega
      rw [foldTR.loop]
      simp only [succ_eq_add_one]
      rw [fold_congr t, foldTR_loop_congr t, go, fold]
      congr
      omega
  go n 0 f

theorem any_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) : any n f = any m (fun i h => f i (by omega)) := by
  subst m
  rfl

private theorem anyTR_loop_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) (j : Nat) (h : j ≤ n) :
    anyTR.loop n f j h = anyTR.loop m (fun i h => f i (by omega)) j (by omega) := by
  subst m
  rfl

@[csimp] theorem any_eq_anyTR : @any = @anyTR :=
  funext fun n => funext fun f =>
  let rec go : ∀ m n f, any (m + n) f = (any n (fun i h => f i (by omega)) || anyTR.loop (m + n) f m (by omega))
    | 0,      n, f => by
      simp [anyTR.loop]
      have t : 0 + n = n := by omega
      rw [any_congr t]
    | succ m, n, f => by
      have t : (m + 1) + n = m + (n + 1) := by omega
      rw [anyTR.loop]
      simp only [succ_eq_add_one]
      rw [any_congr t, anyTR_loop_congr t, go, any, Bool.or_assoc]
      congr
      omega
  go n 0 f

theorem all_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) : all n f = all m (fun i h => f i (by omega)) := by
  subst m
  rfl

private theorem allTR_loop_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) (j : Nat) (h : j ≤ n) : allTR.loop n f j h = allTR.loop m (fun i h => f i (by omega)) j (by omega) := by
  subst m
  rfl

@[csimp] theorem all_eq_allTR : @all = @allTR :=
  funext fun n => funext fun f =>
  let rec go : ∀ m n f, all (m + n) f = (all n (fun i h => f i (by omega)) && allTR.loop (m + n) f m (by omega))
    | 0,      n, f => by
      simp [allTR.loop]
      have t : 0 + n = n := by omega
      rw [all_congr t]
    | succ m, n, f => by
      have t : (m + 1) + n = m + (n + 1) := by omega
      rw [allTR.loop]
      simp only [succ_eq_add_one]
      rw [all_congr t, allTR_loop_congr t, go, all, Bool.and_assoc]
      congr
      omega
  go n 0 f

/-! # `dfold` -/

private def dfoldCast {n : Nat} (α : (i : Nat) → (h : i ≤ n := by omega) → Type u)
    {i j : Nat} {hi : i ≤ n} (w : i = j) (x : α i hi) : α j (by omega) := by
  subst w
  exact x

@[local simp] private theorem dfoldCast_rfl (h : i ≤ n) (w : i = i) (x : α i h) : dfoldCast α w x = x := by
  simp [dfoldCast]

@[local simp] private theorem dfoldCast_trans (h : i ≤ n) (w₁ : i = j) (w₂ : j = k) (x : α i h) :
    dfoldCast @α w₂ (dfoldCast @α w₁ x) = dfoldCast @α (w₁.trans w₂) x := by
  cases w₁
  cases w₂
  simp [dfoldCast]

@[local simp] private theorem dfoldCast_eq_dfoldCast_iff {α : (i : Nat) → (h : i ≤ n := by omega) → Type u} {w₁ w₂ : i = j} {h : i ≤ n} {x : α i h} :
    dfoldCast @α w₁ x = dfoldCast (n := n) (fun i h => α i) (hi := hi) w₂ x ↔ w₁ = w₂ := by
  cases w₁
  cases w₂
  simp [dfoldCast]

private theorem apply_dfoldCast {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α i → α (i + 1)) {i j : Nat} (h : i < n) {w : i = j} {x : α i (by omega)} :
    f j (by omega) (dfoldCast @α w x) = dfoldCast (n := n) (fun i h => α i) (hi := by omega) (by omega) (f i h x) := by
  subst w
  simp

/--
`Nat.dfold` evaluates `f` on the numbers up to `n` exclusive, in increasing order:
* `Nat.dfold f 3 init = init |> f 0 |> f 1 |> f 2`
The input and output types of `f` are indexed by the current index, i.e. `f : (i : Nat) → (h : i < n) → α i → α (i + 1)`.
-/
@[specialize]
def dfold (n : Nat) {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α i → α (i + 1)) (init : α 0) : α n :=
  let rec @[specialize] loop : ∀ j, j ≤ n → α (n - j) → α n
    | 0,      h, a => a
    | succ m, h, a =>
      loop m (by omega) (dfoldCast @α (by omega) (f (n - succ m) (by omega) a))
  loop n (by omega) (dfoldCast @α (by omega) init)

/--
`Nat.dfoldRev` evaluates `f` on the numbers up to `n` exclusive, in decreasing order:
* `Nat.dfoldRev f 3 init = f 0 <| f 1 <| f 2 <| init`
The input and output types of `f` are indexed by the current index, i.e. `f : (i : Nat) → (h : i < n) → α (i + 1) → α i`.
-/
@[specialize]
def dfoldRev (n : Nat) {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α (i + 1) → α i) (init : α n) : α 0 :=
  match n with
  | 0       => init
  | (n + 1) => dfoldRev n (α := fun i h => α i) (fun i h => f i (by omega)) (f n (by omega) init)

/-! # Theorems -/

/-! ### `fold` -/

@[simp] theorem fold_zero {α : Type u} (f : (i : Nat) → i < 0 → α → α) (init : α) :
    fold 0 f init = init := by simp [fold]

@[simp] theorem fold_succ {α : Type u} (n : Nat) (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    fold (n + 1) f init = f n (by omega) (fold n (fun i h => f i (by omega)) init) := by simp [fold]

@[grind =] theorem fold_eq_finRange_foldl {α : Type u} (n : Nat) (f : (i : Nat) → i < n → α → α) (init : α) :
    fold n f init = (List.finRange n).foldl (fun acc ⟨i, h⟩ => f i h acc) init := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [ih, List.finRange_succ_last, List.foldl_map]

theorem fold_add
    {α n m} (f : (i : Nat) → i < n + m → α → α) (init : α) :
    fold (n + m) f init =
      fold m (fun i h => f (n + i) (by omega))
        (fold n (fun i h => f i (by omega)) init) := by
  induction m with
  | zero => simp; rfl
  | succ m ih =>
    simp [fold_congr (Nat.add_assoc n m 1).symm, ih]

/-! ### `foldRev` -/

@[simp] theorem foldRev_zero {α : Type u} (f : (i : Nat) → i < 0 → α → α) (init : α) :
    foldRev 0 f init = init := by simp [foldRev]

@[simp] theorem foldRev_succ {α : Type u} (n : Nat) (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    foldRev (n + 1) f init = foldRev n (fun i h => f i (by omega)) (f n (by omega) init) := by
  simp [foldRev]

@[grind =] theorem foldRev_eq_finRange_foldr {α : Type u} (n : Nat) (f : (i : Nat) → i < n → α → α) (init : α) :
    foldRev n f init = (List.finRange n).foldr (fun ⟨i, h⟩ acc => f i h acc) init := by
  induction n generalizing init with
  | zero => simp
  | succ n ih => simp [ih, List.finRange_succ_last, List.foldr_map]

theorem foldRev_add
    {α n m} (f : (i : Nat) → i < n + m → α → α) (init : α) :
    foldRev (n + m) f init =
      foldRev n (fun i h => f i (by omega))
        (foldRev m (fun i h => f (n + i) (by omega)) init) := by
  induction m generalizing init with
  | zero => simp; rfl
  | succ m ih =>
    rw [foldRev_congr (Nat.add_assoc n m 1).symm]
    simp [ih]

/-! ### `any` -/

@[simp] theorem any_zero {f : (i : Nat) → i < 0 → Bool} : any 0 f = false := by simp [any]

@[simp] theorem any_succ {n : Nat} (f : (i : Nat) → i < n + 1 → Bool) :
    any (n + 1) f = (any n (fun i h => f i (by omega)) || f n (by omega)) := by simp [any]

@[grind =] theorem any_eq_finRange_any {n : Nat} (f : (i : Nat) → i < n → Bool) :
    any n f = (List.finRange n).any (fun ⟨i, h⟩ => f i h) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, List.finRange_succ_last, List.any_map, Function.comp_def]

/-! ### `all` -/

@[simp] theorem all_zero {f : (i : Nat) → i < 0 → Bool} : all 0 f = true := by simp [all]

@[simp] theorem all_succ {n : Nat} (f : (i : Nat) → i < n + 1 → Bool) :
    all (n + 1) f = (all n (fun i h => f i (by omega)) && f n (by omega)) := by simp [all]

@[grind =] theorem all_eq_finRange_all {n : Nat} (f : (i : Nat) → i < n → Bool) :
    all n f = (List.finRange n).all (fun ⟨i, h⟩ => f i h) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, List.finRange_succ_last, List.all_map, Function.comp_def]

/-! ### `dfold` -/

@[simp]
theorem dfold_zero
    {α : (i : Nat) → (h : i ≤ 0 := by omega) → Type u}
    (f : (i : Nat) → (h : i < 0) → α i → α (i + 1)) (init : α 0) :
    dfold 0 f init = init := by
  simp [dfold, dfold.loop]

private theorem dfold_loop_succ
    {α : (i : Nat) → (h : i ≤ n + 1 := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + 1) → α i → α (i + 1))
    (a : α (n + 1 - (j + 1))) (w : j ≤ n):
    dfold.loop (n + 1) f (j + 1) (by omega) a =
      f n (by omega)
        (dfold.loop n (α := fun i h => α i) (fun i h => f i (by omega)) j w (dfoldCast @α (by omega) a)) := by
  induction j with
  | zero => simp [dfold.loop]
  | succ j ih =>
    rw [dfold.loop, ih _ (by omega)]
    congr 2
    simp only [succ_eq_add_one, dfoldCast_trans]
    rw [apply_dfoldCast (h := by omega) f]
    · erw [dfoldCast_trans (h := by omega)]
      erw [dfoldCast_eq_dfoldCast_iff]
      omega

@[simp]
theorem dfold_succ
    {α : (i : Nat) → (h : i ≤ n + 1 := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + 1) → α i → α (i + 1)) (init : α 0) :
    dfold (n + 1) f init =
      f n (by omega) (dfold n (α := fun i h => α i) (fun i h => f i (by omega)) init) := by
  simp [dfold]
  rw [dfold_loop_succ (w := Nat.le_refl _)]
  congr 2
  simp only [dfoldCast_trans]
  erw [dfoldCast_eq_dfoldCast_iff]
  exact le_add_left 0 (n + 1)

-- This isn't a proper `@[congr]` lemma, but it doesn't seem possible to state one.
theorem dfold_congr
    {n m : Nat} (w : n = m)
    {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α i → α (i + 1)) (init : α 0) :
      dfold n f init =
        cast (by subst w; rfl)
          (dfold m (α := fun i h => α i) (fun i h => f i (by omega)) init) := by
  subst w
  rfl

theorem dfold_add
    {α : (i : Nat) → (h : i ≤ n + m := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + m) → α i → α (i + 1)) (init : α 0) :
    dfold (n + m) f init =
      dfold m (α := fun i h => α (n + i)) (fun i h => f (n + i) (by omega))
        (dfold n (α := fun i h => α i) (fun i h => f i (by omega)) init) := by
  induction m with
  | zero => simp; rfl
  | succ m ih =>
    simp [dfold_congr (Nat.add_assoc n m 1).symm, ih]

@[simp] theorem dfoldRev_zero
    {α : (i : Nat) → (h : i ≤ 0 := by omega) → Type u}
    (f : (i : Nat) → (_ : i < 0) → α (i + 1) → α i) (init : α 0) :
    dfoldRev 0 f init = init := by
  simp [dfoldRev]

@[simp] theorem dfoldRev_succ
    {α : (i : Nat) → (h : i ≤ n + 1 := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + 1) → α (i + 1) → α i) (init : α (n + 1)) :
    dfoldRev (n + 1) f init =
      dfoldRev n (α := fun i h => α i) (fun i h => f i (by omega)) (f n (by omega) init) := by
  simp [dfoldRev]

@[congr]
theorem dfoldRev_congr
    {n m : Nat} (w : n = m)
    {α : (i : Nat) → (h : i ≤ n := by omega) → Type u}
    (f : (i : Nat) → (h : i < n) → α (i + 1) → α i) (init : α n) :
      dfoldRev n f init =
        dfoldRev m (α := fun i h => α i) (fun i h => f i (by omega))
          (cast (by subst w; rfl) init) := by
  subst w
  rfl

theorem dfoldRev_add
    {α : (i : Nat) → (h : i ≤ n + m := by omega) → Type u}
    (f : (i : Nat) → (h : i < n + m) → α (i + 1) → α i) (init : α (n + m)) :
    dfoldRev (n + m) f init =
      dfoldRev n (α := fun i h => α i) (fun i h => f i (by omega))
        (dfoldRev m (α := fun i h => α (n + i)) (fun i h => f (n + i) (by omega)) init) := by
  induction m with
  | zero => simp; rfl
  | succ m ih =>
    simp [← Nat.add_assoc, ih]

end Nat

namespace Prod

/--
Combines an initial value with each natural number from a range, in increasing order.

In particular, `(start, stop).foldI f init` applies `f`on all the numbers
from `start` (inclusive) to `stop` (exclusive) in increasing order:

Examples:
* `(5, 8).foldI (fun j _ _ xs => xs.push j) #[] = (#[] |>.push 5 |>.push 6 |>.push 7)`
* `(5, 8).foldI (fun j _ _ xs => xs.push j) #[] = #[5, 6, 7]`
* `(5, 8).foldI (fun j _ _ xs => toString j :: xs) [] = ["7", "6", "5"]`
-/
@[inline, simp] def foldI {α : Type u} (i : Nat × Nat) (f : (j : Nat) → i.1 ≤ j → j < i.2 → α → α) (init : α) : α :=
  (i.2 - i.1).fold (fun j _ => f (i.1 + j) (by omega) (by omega)) init

/--
Checks whether a predicate holds for any natural number in a range.

In particular, `(start, stop).allI f` returns true if `f` is true for any natural number from
`start` (inclusive) to `stop` (exclusive).

Examples:
 * `(5, 8).anyI (fun j _ _ => j == 6) = (5 == 6) || (6 == 6) || (7 == 6)`
 * `(5, 8).anyI (fun j _ _ => j % 2 = 0) = true`
 * `(6, 6).anyI (fun j _ _ => j % 2 = 0) = false`
-/
@[inline, simp] def anyI (i : Nat × Nat) (f : (j : Nat) → i.1 ≤ j → j < i.2 → Bool) : Bool :=
  (i.2 - i.1).any (fun j _ => f (i.1 + j) (by omega) (by omega))

/--
Checks whether a predicate holds for all natural numbers in a range.

In particular, `(start, stop).allI f` returns true if `f` is true for all natural numbers from
`start` (inclusive) to `stop` (exclusive).

Examples:
 * `(5, 8).allI (fun j _ _ => j < 10) = (5 < 10) && (6 < 10) && (7 < 10)`
 * `(5, 8).allI (fun j _ _ => j % 2 = 0) = false`
 * `(6, 7).allI (fun j _ _ => j % 2 = 0) = true`
-/
@[inline, simp] def allI (i : Nat × Nat) (f : (j : Nat) → i.1 ≤ j → j < i.2 → Bool) : Bool :=
  (i.2 - i.1).all (fun j _ => f (i.1 + j) (by omega) (by omega))

end Prod
