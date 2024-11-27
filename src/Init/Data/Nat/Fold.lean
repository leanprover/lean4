/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Kim Morrison
-/
prelude
import Init.Omega

set_option linter.missingDocs true -- keep it documented
universe u

namespace Nat

/--
`Nat.fold` evaluates `f` on the numbers up to `n` exclusive, in increasing order:
* `Nat.fold f 3 init = init |> f 0 |> f 1 |> f 2`
-/
@[specialize] def fold {α : Type u} : (n : Nat) → (f : (i : Nat) → i < n → α → α) → (init : α) → α
  | 0,      f, a => a
  | succ n, f, a => f n (by omega) (fold n (fun i h => f i (by omega)) a)

/-- Tail-recursive version of `Nat.fold`. -/
@[inline] def foldTR {α : Type u} (n : Nat) (f : (i : Nat) → i < n → α → α) (init : α) : α :=
  let rec @[specialize] loop : ∀ j, j ≤ n → α → α
    | 0,      h, a => a
    | succ m, h, a => loop m (by omega) (f (n - succ m) (by omega) a)
  loop n (by omega) init

/--
`Nat.foldRev` evaluates `f` on the numbers up to `n` exclusive, in decreasing order:
* `Nat.foldRev f 3 init = f 0 <| f 1 <| f 2 <| init`
-/
@[specialize] def foldRev {α : Type u} : (n : Nat) → (f : (i : Nat) → i < n → α → α) → (init : α) → α
  | 0,      f, a => a
  | succ n, f, a => foldRev n (fun i h => f i (by omega)) (f n (by omega) a)

/-- `any f n = true` iff there is `i in [0, n-1]` s.t. `f i = true` -/
@[specialize] def any : (n : Nat) → (f : (i : Nat) → i < n → Bool) → Bool
  | 0,      f => false
  | succ n, f => any n (fun i h => f i (by omega)) || f n (by omega)

/-- Tail-recursive version of `Nat.any`. -/
@[inline] def anyTR (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  let rec @[specialize] loop : (i : Nat) → i ≤ n → Bool
    | 0,      h => false
    | succ m, h => f (n - succ m) (by omega) || loop m (by omega)
  loop n (by omega)

/-- `all f n = true` iff every `i in [0, n-1]` satisfies `f i = true` -/
@[specialize] def all : (n : Nat) → (f : (i : Nat) → i < n → Bool) → Bool
  | 0,      f => true
  | succ n, f => all n (fun i h => f i (by omega)) && f n (by omega)

/-- Tail-recursive version of `Nat.all`. -/
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

theorem foldTR_loop_congr {α : Type u} {n m : Nat} (w : n = m)
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
      simp only [succ_eq_add_one, Nat.add_sub_cancel]
      rw [fold_congr t, foldTR_loop_congr t, go, fold]
      congr
      omega
  go n 0 f

theorem any_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) : any n f = any m (fun i h => f i (by omega)) := by
  subst m
  rfl

theorem anyTR_loop_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) (j : Nat) (h : j ≤ n) :
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

theorem allTR_loop_congr {n m : Nat} (w : n = m) (f : (i : Nat) → i < n → Bool) (j : Nat) (h : j ≤ n) : allTR.loop n f j h = allTR.loop m (fun i h => f i (by omega)) j (by omega) := by
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

theorem fold_eq_range_fold {α : Type u} (n : Nat) (f : (i : Nat) → i < n → α → α) (init : α) :
    fold n f init = (List.finRange n).foldr (fun i acc => f i (by simp; omega) acc) init := by
  sorry

end Nat

namespace Prod

/--
`(start, stop).foldI f a` evaluates `f` on all the numbers
from `start` (inclusive) to `stop` (exclusive) in increasing order:
* `(5, 8).foldI f init = init |> f 5 |> f 6 |> f 7`
-/
@[inline] def foldI {α : Type u} (i : Nat × Nat) (f : (j : Nat) → i.1 ≤ j → j < i.2 → α → α) (a : α) : α :=
  (i.2 - i.1).fold (fun j _ => f (i.1 + j) (by omega) (by omega)) a

/--
`(start, stop).anyI f a` returns true if `f` is true for some natural number
from `start` (inclusive) to `stop` (exclusive):
* `(5, 8).anyI f = f 5 || f 6 || f 7`
-/
@[inline] def anyI (i : Nat × Nat) (f : (j : Nat) → i.1 ≤ j → j < i.2 → Bool) : Bool :=
  (i.2 - i.1).any (fun j _ => f (i.1 + j) (by omega) (by omega))

/--
`(start, stop).allI f a` returns true if `f` is true for all natural numbers
from `start` (inclusive) to `stop` (exclusive):
* `(5, 8).anyI f = f 5 && f 6 && f 7`
-/
@[inline] def allI (i : Nat × Nat) (f : (j : Nat) → i.1 ≤ j → j < i.2 → Bool) : Bool :=
  (i.2 - i.1).all (fun j _ => f (i.1 + j) (by omega) (by omega))

end Prod
