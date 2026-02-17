/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro, Chad Sharp
-/
module

prelude
public import Init.Data.List.Scan.Basic
public import Init.Data.List.Lemmas
import all Init.Data.List.Scan.Basic
import Init.Data.List.TakeDrop
import Init.Data.Option.Lemmas
import Init.Data.Nat.Lemmas

public section

/-!
# List scan

Prove basic results about `List.scanl`, `List.scanr`, `List.scanlM` and `List.scanrM`.
-/

namespace List

/-! ### `List.scanlM` and `List.scanrM` -/

@[local simp]
private theorem scanAuxM.go_eq_append_map [Monad m] [LawfulMonad m] {f : α → β → m α} :
    go f xs last acc = (· ++ acc) <$> scanAuxM f last xs := by
  unfold scanAuxM
  induction xs generalizing last acc with
  | nil => simp [scanAuxM.go]
  | cons _ _ ih => simp [scanAuxM.go, ih (acc := last :: acc), ih (acc := [last])]

private theorem scanAuxM_nil [Monad m] {f : α → β → m α} :
    scanAuxM f init [] = return [init] := rfl

private theorem scanAuxM_cons [Monad m] [LawfulMonad m] {f : α → β → m α} :
    scanAuxM f init (x :: xs) = return (← scanAuxM f (← f init x) xs) ++ [init] := by
  rw [scanAuxM, scanAuxM.go]
  simp

@[simp, grind =]
theorem scanlM_nil [Monad m] [LawfulMonad m] {f : α → β → m α} :
    scanlM f init [] = return [init] := by
  simp [scanlM, scanAuxM_nil]

@[simp, grind =]
theorem scanlM_cons [Monad m] [LawfulMonad m] {f : α → β → m α} :
    scanlM f init (x :: xs) = return init :: (← scanlM f (← f init x) xs) := by
  simp [scanlM, scanAuxM_cons]

@[simp, grind =]
theorem scanrM_concat [Monad m] [LawfulMonad m] {f : α → β → m β} :
    scanrM f init (xs ++ [x]) = return (← scanrM f (← f x init) xs) ++ [init] := by
  simp [scanrM, flip, scanAuxM_cons]

@[simp, grind =]
theorem scanrM_nil [Monad m] {f : α → β → m β} :
    scanrM f init [] = return [init] :=
  (rfl)

theorem scanlM_eq_scanrM_reverse [Monad m] {f : β → α → m β} :
    scanlM f init as = reverse <$> (scanrM (flip f) init as.reverse) := by
  simp only [scanrM, reverse_reverse]
  rfl

theorem scanrM_eq_scanlM_reverse [Monad m] [LawfulMonad m] {f : α → β → m β} :
    scanrM f init as = reverse <$> (scanlM (flip f) init as.reverse) := by
  simp only [scanlM_eq_scanrM_reverse, reverse_reverse, id_map', Functor.map_map]
  rfl

@[simp, grind =]
theorem scanrM_reverse [Monad m] [LawfulMonad m] {f : α → β → m β} :
    scanrM f init as.reverse = reverse <$> (scanlM (flip f) init as) := by
  simp [scanrM_eq_scanlM_reverse (as := as.reverse)]

@[simp, grind =]
theorem scanlM_reverse [Monad m] {f : β → α → m β} :
    scanlM f init as.reverse = reverse <$> (scanrM (flip f) init as) := by
  simp [scanlM_eq_scanrM_reverse (as := as.reverse)]

theorem scanlM_pure [Monad m] [LawfulMonad m] {f: β → α → β} {as : List α} :
    as.scanlM (m := m) (pure <| f · ·) init = pure (as.scanl f init) := by
  induction as generalizing init with simp_all [scanlM_cons, scanl]

theorem scanrM_pure [Monad m] [LawfulMonad m] {f : α → β → β} {as : List α} :
    as.scanrM (m := m) (pure <| f · · ) init = pure (as.scanr f init) := by
  simp only [scanrM_eq_scanlM_reverse]
  unfold flip
  simp only [scanlM_pure, map_pure, scanr,  scanrM_eq_scanlM_reverse]
  rfl

theorem idRun_scanlM {f : β → α → Id β} {as : List α} :
    (as.scanlM f init).run = as.scanl (f · · |>.run) init :=
  scanlM_pure

theorem idRun_scanrM {f : α → β → Id β} {as : List α} :
    (as.scanrM f init).run = as.scanr (f · · |>.run) init :=
  scanrM_pure

@[simp, grind =]
theorem scanlM_map [Monad m] [LawfulMonad m]
    {f : α₁ → α₂} {g: β → α₂ → m β} {as : List α₁} :
    (as.map f).scanlM g init = as.scanlM (g · <| f ·) init := by
  induction as generalizing g init with simp [*]

@[simp, grind =]
theorem scanrM_map [Monad m] [LawfulMonad m]
    {f : α₁ → α₂} {g: α₂ → β → m β} {as : List α₁} :
    (as.map f).scanrM g init = as.scanrM (fun a b => g (f a) b) init := by
  simp only [← map_reverse, scanlM_map, scanrM_eq_scanlM_reverse]
  rfl

/-! ### `List.scanl` and `List.scanr` -/

@[simp]
theorem length_scanl {f : β → α → β} : (scanl f init as).length = as.length + 1 := by
  induction as generalizing init <;> simp_all [scanl, pure, bind, Id.run]

grind_pattern length_scanl => scanl f init as

@[simp, grind =]
theorem scanl_nil {f : β → α → β} : scanl f init [] = [init] := by simp [scanl]

@[simp, grind =]
theorem scanl_cons {f : β → α → β} : scanl f b (a :: l) = b :: scanl f (f b a) l := by
  simp [scanl]

theorem scanl_singleton {f : β → α → β} : scanl f b [a] = [b, f b a] := by simp

@[simp]
theorem scanl_ne_nil {f : β → α → β} : scanl f b l ≠ [] := by
  cases l <;> simp

@[simp]
theorem scanl_iff_nil {f : β → α → β} (c : β) : scanl f b l = [c] ↔ c = b ∧ l = [] := by
  cases l
  · simp [eq_comm]
  · simp

@[simp, grind =]
theorem getElem_scanl {f : α → β → α} (h : i < (scanl f a l).length) :
    (scanl f a l)[i] = foldl f a (l.take i) := by
  induction l generalizing a i
  · simp
  · cases i <;> simp [*]

@[grind =]
theorem getElem?_scanl {f : α → β → α} :
    (scanl f a l)[i]? = if i ≤ l.length then some (foldl f a (l.take i)) else none := by
  split
  · rw [getElem?_pos _ _ (by simpa using Nat.lt_add_one_iff.mpr ‹_›), getElem_scanl]
  · rw [getElem?_neg]
    simpa only [length_scanl, Nat.lt_add_one_iff]

@[grind _=_]
theorem take_scanl {f : β → α → β} (init : β) (as : List α) (i : Nat) :
    (scanl f init as).take (i + 1) = scanl f init (as.take i) := by
  induction as generalizing init i
  · simp
  · cases i
    · simp
    · simp [*]

theorem getElem?_scanl_zero {f : β → α → β} : (scanl f b l)[0]? = some b := by
  simp

theorem getElem_scanl_zero {f : β → α → β} : (scanl f b l)[0] = b := by
  simp

@[simp]
theorem head_scanl {f : β → α → β} (h : scanl f b l ≠ []) : (scanl f b l).head h = b := by
  simp [head_eq_getElem]

@[simp]
theorem head?_scanl {f : β → α → β} : (scanl f b l).head? = some b := by
  simp [head?_eq_getElem?]

theorem getLast_scanl {f : β → α → β} (h : scanl f b l ≠ []) :
    (scanl f b l).getLast h = foldl f b l := by
  simp [getLast_eq_getElem]

theorem getLast?_scanl {f : β → α → β} : (scanl f b l).getLast? = some (foldl f b l) := by
  simp [getLast?_eq_getElem?]

@[grind =]
theorem tail_scanl {f : β → α → β} (h : 0 < l.length) :
    (scanl f b l).tail = scanl f (f b (l.head (ne_nil_of_length_pos h))) l.tail := by
  induction l
  · simp at h
  · simp

theorem getElem?_succ_scanl {f : β → α → β} :
    (scanl f b l)[i + 1]? = (scanl f b l)[i]?.bind fun x => l[i]?.map fun y => f x y := by
  simp only [getElem?_scanl, take_add_one]
  split
  · have : i < l.length := Nat.add_one_le_iff.mp ‹_›
    have : i ≤ l.length := Nat.le_of_lt ‹_›
    simp [*, - take_append_getElem]
  · split
    · apply Eq.symm
      simpa using Nat.lt_add_one_iff.mp (Nat.not_le.mp ‹_›)
    · simp

theorem getElem_succ_scanl {f : β → α → β} (h : i + 1 < (scanl f b l).length) :
    (scanl f b l)[i + 1] = f ((l.scanl f b)[i]'(Nat.lt_trans (Nat.lt_add_one _) h)) (l[i]'(by simpa using h)) := by
  simp only [length_scanl, Nat.add_lt_add_iff_right] at h
  simp [take_add_one, *, - take_append_getElem]

@[grind =]
theorem scanl_append {f : β → α → β} {l₁ l₂ : List α} :
    scanl f b (l₁ ++ l₂) = scanl f b l₁ ++ (scanl f (foldl f b l₁) l₂).tail := by
  induction l₁ generalizing b
  case nil => cases l₂ <;> simp
  case cons head tail ih => simp [ih]

@[grind =]
theorem scanl_map {f : β → γ → β} {g : α → γ} {as : List α} :
    scanl f init (as.map g) = scanl (fun acc x => f acc (g x)) init as := by
  induction as generalizing init with simp [*]

theorem scanl_eq_scanr_reverse {f : β → α → β} :
    scanl f init as = reverse (scanr (flip f) init as.reverse) := by
  simp only [scanl, scanr, Id.run, scanrM_reverse, Functor.map, reverse_reverse]
  rfl

theorem scanr_eq_scanl_reverse  {f : α → β → β} :
    scanr f init as = reverse (scanl (flip f) init as.reverse) := by
  simp only [scanl_eq_scanr_reverse, reverse_reverse]
  rfl

@[simp, grind =]
theorem scanl_reverse {f : β → α → β} {as : List α} :
    scanl f init as.reverse = reverse (scanr (flip f) init as) := by
  simp [scanr_eq_scanl_reverse]

@[simp, grind =]
theorem scanr_reverse {f : α → β → β} {as : List α} :
    scanr f init as.reverse = reverse (scanl (flip f) init as) := by
  simp [scanl_eq_scanr_reverse]

@[simp, grind =]
theorem scanr_nil {f : α → β → β} : scanr f init [] = [init] := by simp [scanr]

@[simp, grind =]
theorem scanr_cons {f : α → β → β} :
    scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp [scanr_eq_scanl_reverse, reverse_cons, scanl_append, flip, - scanl_reverse]

@[simp]
theorem scanr_ne_nil {f : α → β → β} : scanr f b l ≠ [] := by
  simp [scanr_eq_scanl_reverse, - scanl_reverse]

theorem scanr_singleton {f : α → β → β} : scanr f b [a] = [f a b, b] := by
  simp

@[simp]
theorem length_scanr {f : α → β → β} {as : List α} :
    length (scanr f init as) = as.length + 1 := by
  simp [scanr_eq_scanl_reverse, - scanl_reverse]

grind_pattern length_scanr => scanr f init as

@[simp]
theorem scanr_iff_nil {f : α → β → β} (c : β) : scanr f b l = [c] ↔ c = b ∧ l = [] := by
  simp [scanr_eq_scanl_reverse, - scanl_reverse]

@[grind =]
theorem scanr_append {f : α → β → β} (l₁ l₂ : List α) :
    scanr f b (l₁ ++ l₂) = (scanr f (foldr f b l₂) l₁) ++ (scanr f b l₂).tail := by
  induction l₁ <;> induction l₂ <;> simp [*]

@[simp]
theorem head_scanr {f : α → β → β} (h : scanr f b l ≠ []) :
    (scanr f b l).head h = foldr f b l := by
  simp [scanr_eq_scanl_reverse, - scanl_reverse, getLast_scanl, flip]

@[grind =]
theorem getLast_scanr {f : α → β → β} (h : scanr f b l ≠ []) :
    (scanr f b l).getLast h = b := by
  simp [scanr_eq_scanl_reverse, - scanl_reverse]

theorem getLast?_scanr {f : α → β → β} : (scanr f b l).getLast? = some b := by
  simp [scanr_eq_scanl_reverse, - scanl_reverse]

@[grind =]
theorem tail_scanr {f : α → β → β} (h : 0 < l.length) :
    (scanr f b l).tail = scanr f b l.tail := by
  induction l with simp_all

@[grind _=_]
theorem drop_scanr {f : α → β → β} (h : i ≤ l.length) :
    (scanr f b l).drop i = scanr f b (l.drop i) := by
  induction i generalizing l
  · simp
  · rename_i i ih
    rw [drop_add_one_eq_tail_drop (i := i), drop_add_one_eq_tail_drop (i := i), ih]
    · rw [tail_scanr]
      simpa [length_drop, Nat.lt_sub_iff_add_lt]
    · exact Nat.le_of_lt (Nat.add_one_le_iff.mp ‹_›)

@[simp, grind =]
theorem getElem_scanr {f : α → β → β} (h : i < (scanr f b l).length) :
    (scanr f b l)[i] = foldr f b (l.drop i) := by
  induction l generalizing b i
  · simp
  · cases i <;> simp [*]

@[grind =]
theorem getElem?_scanr {f : α → β → β} :
    (scanr f b l)[i]? = if i < l.length + 1 then some (foldr f b (l.drop i)) else none := by
  split
  · rw [getElem?_pos _ _ (by simpa), getElem_scanr]
  · rename_i h
    simpa [getElem?_neg, length_scanr] using h

@[simp]
theorem head?_scanr {f : α → β → β} : (scanr f b l).head? = some (foldr f b l) := by
  simp [head?_eq_getElem?]

theorem getElem_scanr_zero {f : α → β → β} : (scanr f b l)[0] = foldr f b l := by
  simp

theorem getElem?_scanr_zero {f : α → β → β} : (scanr f b l)[0]? = some (foldr f b l) := by
  simp

theorem getElem?_scanr_of_lt {f : α → β → β} (h : i < l.length + 1) :
    (scanr f b l)[i]? = some (foldr f b (l.drop i)) := by
  simp [h]

@[grind =]
theorem scanr_map {f : α → β → β} {g : γ → α} (b : β) (l : List γ) :
    scanr f b (l.map g) = scanr (fun x acc => f (g x) acc) b l := by
  suffices ∀ l, foldr f b (l.map g) = foldr (fun x acc => f (g x) acc) b l from by
    induction l generalizing b with simp [*]
  intro l
  induction l with simp [*]
