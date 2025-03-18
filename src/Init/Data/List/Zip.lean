/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.TakeDrop
import Init.Data.Function

/-!
# Lemmas about `List.zip`, `List.zipWith`, `List.zipWithAll`, and `List.unzip`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ## Zippers -/

/-! ### zipWith -/

theorem zipWith_comm (f : α → β → γ) :
    ∀ (as : List α) (bs : List β), zipWith f as bs = zipWith (fun b a => f a b) bs as
  | [], _ => List.zipWith_nil_right.symm
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => congrArg _ (zipWith_comm f as bs)

theorem zipWith_comm_of_comm (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : List α) :
    zipWith f l l' = zipWith f l' l := by
  rw [zipWith_comm]
  simp only [comm]

@[simp]
theorem zipWith_self (f : α → α → δ) : ∀ l : List α, zipWith f l l = l.map fun a => f a a
  | [] => rfl
  | _ :: xs => congrArg _ (zipWith_self f xs)

@[deprecated zipWith_self (since := "2025-01-29")] abbrev zipWith_same := @zipWith_self

/--
See also `getElem?_zipWith'` for a variant
using `Option.map` and `Option.bind` rather than a `match`.
-/
theorem getElem?_zipWith {f : α → β → γ} {i : Nat} :
    (zipWith f as bs)[i]? = match as[i]?, bs[i]? with
      | some a, some b => some (f a b) | _, _ => none := by
  induction as generalizing bs i with
  | nil => cases bs with
    | nil => simp
    | cons b bs => simp
  | cons a as aih => cases bs with
    | nil => simp
    | cons b bs => cases i <;> simp_all

/-- Variant of `getElem?_zipWith` using `Option.map` and `Option.bind` rather than a `match`. -/
theorem getElem?_zipWith' {f : α → β → γ} {i : Nat} :
    (zipWith f l₁ l₂)[i]? = (l₁[i]?.map f).bind fun g => l₂[i]?.map g := by
  induction l₁ generalizing l₂ i with
  | nil => rw [zipWith] <;> simp
  | cons _ _ =>
    cases l₂
    · simp
    · cases i <;> simp_all

theorem getElem?_zipWith_eq_some {f : α → β → γ} {l₁ : List α} {l₂ : List β} {z : γ} {i : Nat} :
    (zipWith f l₁ l₂)[i]? = some z ↔
      ∃ x y, l₁[i]? = some x ∧ l₂[i]? = some y ∧ f x y = z := by
  induction l₁ generalizing l₂ i
  · simp
  · cases l₂ <;> cases i <;> simp_all

theorem getElem?_zip_eq_some {l₁ : List α} {l₂ : List β} {z : α × β} {i : Nat} :
    (zip l₁ l₂)[i]? = some z ↔ l₁[i]? = some z.1 ∧ l₂[i]? = some z.2 := by
  cases z
  rw [zip, getElem?_zipWith_eq_some]; constructor
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    simpa [h₀, h₁] using h₂
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, _, h₀, h₁, rfl⟩

theorem head?_zipWith {f : α → β → γ} :
    (List.zipWith f as bs).head? = match as.head?, bs.head? with
      | some a, some b => some (f a b) | _, _ => none := by
  simp [head?_eq_getElem?, getElem?_zipWith]

theorem head_zipWith {f : α → β → γ} (h):
    (List.zipWith f as bs).head h = f (as.head (by rintro rfl; simp_all)) (bs.head (by rintro rfl; simp_all)) := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_zipWith, head?_eq_head, head?_eq_head]

@[simp]
theorem zipWith_map {μ} (f : γ → δ → μ) (g : α → γ) (h : β → δ) (l₁ : List α) (l₂ : List β) :
    zipWith f (l₁.map g) (l₂.map h) = zipWith (fun a b => f (g a) (h b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_map_left (l₁ : List α) (l₂ : List β) (f : α → α') (g : α' → β → γ) :
    zipWith g (l₁.map f) l₂ = zipWith (fun a b => g (f a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_map_right (l₁ : List α) (l₂ : List β) (f : β → β') (g : α → β' → γ) :
    zipWith g l₁ (l₂.map f) = zipWith (fun a b => g a (f b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_foldr_eq_zip_foldr {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldr g i = (zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWith_foldl_eq_zip_foldl {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldl g i = (zip l₁ l₂).foldl (fun r p => g r (f p.1 p.2)) i := by
  induction l₁ generalizing i l₂ <;> cases l₂ <;> simp_all

@[simp]
theorem zipWith_eq_nil_iff {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  cases l <;> cases l' <;> simp

theorem map_zipWith {δ : Type _} (f : α → β) (g : γ → δ → α) (l : List γ) (l' : List δ) :
    map f (zipWith g l l') = zipWith (fun x y => f (g x y)) l l' := by
  induction l generalizing l' with
  | nil => simp
  | cons hd tl hl =>
    · cases l'
      · simp
      · simp [hl]

theorem take_zipWith : (zipWith f l l').take i = zipWith f (l.take i) (l'.take i) := by
  induction l generalizing l' i with
  | nil => simp
  | cons hd tl hl =>
    cases l'
    · simp
    · cases i
      · simp
      · simp [hl]

@[deprecated take_zipWith (since := "2024-07-26")] abbrev zipWith_distrib_take := @take_zipWith

theorem drop_zipWith : (zipWith f l l').drop i = zipWith f (l.drop i) (l'.drop i) := by
  induction l generalizing l' i with
  | nil => simp
  | cons hd tl hl =>
    · cases l'
      · simp
      · cases i
        · simp
        · simp [hl]

@[deprecated drop_zipWith (since := "2024-07-26")] abbrev zipWith_distrib_drop := @drop_zipWith

@[simp]
theorem tail_zipWith : (zipWith f l l').tail = zipWith f l.tail l'.tail := by
  rw [← drop_one]; simp [drop_zipWith]

@[deprecated tail_zipWith (since := "2024-07-28")] abbrev zipWith_distrib_tail := @tail_zipWith

theorem zipWith_append (f : α → β → γ) (l₁ l₁' : List α) (l₂ l₂' : List β)
    (h : l₁.length = l₂.length) :
    zipWith f (l₁ ++ l₁') (l₂ ++ l₂') = zipWith f l₁ l₂ ++ zipWith f l₁' l₂' := by
  induction l₁ generalizing l₂ with
  | nil =>
    have : l₂ = [] := eq_nil_of_length_eq_zero (by simpa using h.symm)
    simp [this]
  | cons hl tl ih =>
    cases l₂ with
    | nil => simp at h
    | cons _ _ =>
      simp only [length_cons, Nat.succ.injEq] at h
      simp [ih _ h]

theorem zipWith_eq_cons_iff {f : α → β → γ} {l₁ : List α} {l₂ : List β} :
    zipWith f l₁ l₂ = g :: l ↔
      ∃ a l₁' b l₂', l₁ = a :: l₁' ∧ l₂ = b :: l₂' ∧ g = f a b ∧ l = zipWith f l₁' l₂' := by
  match l₁, l₂ with
  | [], [] => simp
  | [], b :: l₂ => simp
  | a :: l₁, [] => simp
  | a' :: l₁, b' :: l₂ =>
    simp only [zip_cons_cons, cons.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨rfl, rfl⟩, rfl⟩
      refine ⟨a', l₁, b', l₂, by simp⟩
    · rintro ⟨a, l₁, b, l₂, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      simp

theorem zipWith_eq_append_iff {f : α → β → γ} {l₁ : List α} {l₂ : List β} :
    zipWith f l₁ l₂ = l₁' ++ l₂' ↔
      ∃ ws xs ys zs, ws.length = ys.length ∧ l₁ = ws ++ xs ∧ l₂ = ys ++ zs ∧ l₁' = zipWith f ws ys ∧ l₂' = zipWith f xs zs := by
  induction l₁ generalizing l₂ l₁' with
  | nil =>
    simp
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨[], [], [], by simp⟩
    · rintro ⟨_, _, _, -, ⟨rfl, rfl⟩, _, rfl, rfl, rfl⟩
      simp
  | cons x₁ l₁ ih₁ =>
    cases l₂ with
    | nil =>
      constructor
      · simp only [zipWith_nil_right, nil_eq, append_eq_nil_iff, exists_and_left, and_imp]
        rintro rfl  rfl
        exact ⟨[], x₁ :: l₁, [], by simp⟩
      · rintro ⟨_, _, _, _, h₁, _, h₃, rfl, rfl⟩
        simp only [nil_eq, append_eq_nil_iff] at h₃
        obtain ⟨rfl, rfl⟩ := h₃
        simp
    | cons x₂ l₂ =>
      simp only [zipWith_cons_cons]
      rw [cons_eq_append_iff]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨_, rfl, h⟩)
        · exact ⟨[], x₁ :: l₁, [], x₂ :: l₂, by simp⟩
        · rw [ih₁] at h
          obtain ⟨ws, xs, ys, zs, h, rfl, rfl, h', rfl⟩ := h
          refine ⟨x₁ :: ws, xs, x₂ :: ys, zs, by simp [h, h']⟩
      · rintro ⟨_, _, _, _, h₁, h₂, h₃, rfl, rfl⟩
        rw [cons_eq_append_iff] at h₂
        rw [cons_eq_append_iff] at h₃
        obtain (⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩) := h₂
        · simp only [zipWith_nil_left, true_and, nil_eq, reduceCtorEq, false_and, exists_const,
          or_false]
          obtain (⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩) := h₃
          · simp
          · simp_all
        · obtain (⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩) := h₃
          · simp_all
          · simp_all [zipWith_append, Nat.succ_inj']

/-- See also `List.zipWith_replicate` in `Init.Data.List.TakeDrop` for a generalization with different lengths. -/
@[simp] theorem zipWith_replicate' {a : α} {b : β} {n : Nat} :
    zipWith f (replicate n a) (replicate n b) = replicate n (f a b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicate_succ, ih]

theorem map_uncurry_zip_eq_zipWith (f : α → β → γ) (l : List α) (l' : List β) :
    map (Function.uncurry f) (l.zip l') = zipWith f l l' := by
  rw [zip]
  induction l generalizing l' with
  | nil => simp
  | cons hl tl ih =>
    cases l' <;> simp [ih]

theorem map_zip_eq_zipWith (f : α × β → γ) (l : List α) (l' : List β) :
    map f (l.zip l') = zipWith (Function.curry f) l l' := by
  rw [zip]
  induction l generalizing l' with
  | nil => simp
  | cons hl tl ih =>
    cases l' <;> simp [ih]

/-! ### zip -/

theorem zip_eq_zipWith : ∀ (l₁ : List α) (l₂ : List β), zip l₁ l₂ = zipWith Prod.mk l₁ l₂
  | [], _ => rfl
  | _, [] => rfl
  | a :: l₁, b :: l₂ => by simp [zip_cons_cons, zip_eq_zipWith l₁ l₂]

theorem zip_map (f : α → γ) (g : β → δ) :
    ∀ (l₁ : List α) (l₂ : List β), zip (l₁.map f) (l₂.map g) = (zip l₁ l₂).map (Prod.map f g)
  | [], _ => rfl
  | _, [] => by simp only [map, zip_nil_right]
  | _ :: _, _ :: _ => by simp only [map, zip_cons_cons, zip_map, Prod.map]

theorem zip_map_left (f : α → γ) (l₁ : List α) (l₂ : List β) :
    zip (l₁.map f) l₂ = (zip l₁ l₂).map (Prod.map f id) := by rw [← zip_map, map_id]

theorem zip_map_right (f : β → γ) (l₁ : List α) (l₂ : List β) :
    zip l₁ (l₂.map f) = (zip l₁ l₂).map (Prod.map id f) := by rw [← zip_map, map_id]

@[simp] theorem tail_zip (l₁ : List α) (l₂ : List β) :
    (zip l₁ l₂).tail = zip l₁.tail l₂.tail := by
  cases l₁ <;> cases l₂ <;> simp

theorem zip_append :
    ∀ {l₁ r₁ : List α} {l₂ r₂ : List β} (_h : length l₁ = length l₂),
      zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂
  | [], _, _, _, h => by simp only [eq_nil_of_length_eq_zero h.symm]; rfl
  | _, _, [], _, h => by simp only [eq_nil_of_length_eq_zero h]; rfl
  | _ :: _, _, _ :: _, _, h => by
    simp only [cons_append, zip_cons_cons, zip_append (Nat.succ.inj h)]

theorem zip_map' (f : α → β) (g : α → γ) :
    ∀ l : List α, zip (l.map f) (l.map g) = l.map fun a => (f a, g a)
  | [] => rfl
  | a :: l => by simp only [map, zip_cons_cons, zip_map']

theorem of_mem_zip {a b} : ∀ {l₁ : List α} {l₂ : List β}, (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂
  | _ :: l₁, _ :: l₂, h => by
    cases h
    case head => simp
    case tail h =>
    · have := of_mem_zip h
      exact ⟨Mem.tail _ this.1, Mem.tail _ this.2⟩

@[deprecated of_mem_zip (since := "2024-07-28")] abbrev mem_zip := @of_mem_zip

theorem map_fst_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length ≤ l₂.length → map Prod.fst (zip l₁ l₂) = l₁
  | [], _, _ => rfl
  | _ :: as, _ :: bs, h => by
    simp [Nat.succ_le_succ_iff] at h
    show _ :: map Prod.fst (zip as bs) = _ :: as
    rw [map_fst_zip as bs h]
  | _ :: _, [], h => by simp at h

theorem map_snd_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₂.length ≤ l₁.length → map Prod.snd (zip l₁ l₂) = l₂
  | _, [], _ => by
    rw [zip_nil_right]
    rfl
  | [], b :: bs, h => by simp at h
  | a :: as, b :: bs, h => by
    simp [Nat.succ_le_succ_iff] at h
    show _ :: map Prod.snd (zip as bs) = _ :: bs
    rw [map_snd_zip as bs h]

theorem map_prod_left_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (x, f x)) = l.zip (l.map f) := by
  rw [← zip_map']
  congr
  simp

theorem map_prod_right_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (f x, x)) = (l.map f).zip l := by
  rw [← zip_map']
  congr
  simp

@[simp] theorem zip_eq_nil_iff {l₁ : List α} {l₂ : List β} :
    zip l₁ l₂ = [] ↔ l₁ = [] ∨ l₂ = [] := by
  simp [zip_eq_zipWith]

theorem zip_eq_cons_iff {l₁ : List α} {l₂ : List β} :
    zip l₁ l₂ = (a, b) :: l ↔
      ∃ l₁' l₂', l₁ = a :: l₁' ∧ l₂ = b :: l₂' ∧ l = zip l₁' l₂' := by
  simp only [zip_eq_zipWith, zipWith_eq_cons_iff]
  constructor
  · rintro ⟨a, l₁, b, l₂, rfl, rfl, h, rfl, rfl⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  · rintro ⟨l₁', l₂', rfl, rfl, rfl⟩
    refine ⟨a, l₁', b, l₂', by simp⟩

theorem zip_eq_append_iff {l₁ : List α} {l₂ : List β} :
    zip l₁ l₂ = l₁' ++ l₂' ↔
      ∃ ws xs ys zs, ws.length = ys.length ∧ l₁ = ws ++ xs ∧ l₂ = ys ++ zs ∧ l₁' = zip ws ys ∧ l₂' = zip xs zs := by
  simp [zip_eq_zipWith, zipWith_eq_append_iff]

/-- See also `List.zip_replicate` in `Init.Data.List.TakeDrop` for a generalization with different lengths. -/
@[simp] theorem zip_replicate' {a : α} {b : β} {n : Nat} :
    zip (replicate n a) (replicate n b) = replicate n (a, b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicate_succ, ih]

/-! ### zipWithAll -/

theorem getElem?_zipWithAll {f : Option α → Option β → γ} {i : Nat} :
    (zipWithAll f as bs)[i]? = match as[i]?, bs[i]? with
      | none, none => .none | a?, b? => some (f a? b?) := by
  induction as generalizing bs i with
  | nil => induction bs generalizing i with
    | nil => simp
    | cons b bs bih => cases i <;> simp_all
  | cons a as aih => cases bs with
    | nil =>
      specialize @aih []
      cases i <;> simp_all
    | cons b bs => cases i <;> simp_all

theorem head?_zipWithAll {f : Option α → Option β → γ} :
    (zipWithAll f as bs).head? = match as.head?, bs.head? with
      | none, none => .none | a?, b? => some (f a? b?) := by
  simp [head?_eq_getElem?, getElem?_zipWithAll]

@[simp] theorem head_zipWithAll {f : Option α → Option β → γ} (h) :
    (zipWithAll f as bs).head h = f as.head? bs.head? := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_zipWithAll]
  split <;> simp_all

@[simp] theorem tail_zipWithAll {f : Option α → Option β → γ} :
    (zipWithAll f as bs).tail = zipWithAll f as.tail bs.tail := by
  cases as <;> cases bs <;> simp

theorem zipWithAll_map {μ} (f : Option γ → Option δ → μ) (g : α → γ) (h : β → δ) (l₁ : List α) (l₂ : List β) :
    zipWithAll f (l₁.map g) (l₂.map h) = zipWithAll (fun a b => f (g <$> a) (h <$> b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWithAll_map_left (l₁ : List α) (l₂ : List β) (f : α → α') (g : Option α' → Option β → γ) :
    zipWithAll g (l₁.map f) l₂ = zipWithAll (fun a b => g (f <$> a) b) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem zipWithAll_map_right (l₁ : List α) (l₂ : List β) (f : β → β') (g : Option α → Option β' → γ) :
    zipWithAll g l₁ (l₂.map f) = zipWithAll (fun a b => g a (f <$> b)) l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem map_zipWithAll {δ : Type _} (f : α → β) (g : Option γ → Option δ → α) (l : List γ) (l' : List δ) :
    map f (zipWithAll g l l') = zipWithAll (fun x y => f (g x y)) l l' := by
  induction l generalizing l' with
  | nil => simp
  | cons hd tl hl =>
    cases l' <;> simp_all

@[simp] theorem zipWithAll_replicate {a : α} {b : β} {n : Nat} :
    zipWithAll f (replicate n a) (replicate n b) = replicate n (f a b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicate_succ, ih]

/-! ### unzip -/

@[simp] theorem unzip_fst : (unzip l).fst = l.map Prod.fst := by
  induction l <;> simp_all

@[simp] theorem unzip_snd : (unzip l).snd = l.map Prod.snd := by
  induction l <;> simp_all

@[deprecated unzip_fst (since := "2024-07-28")] abbrev unzip_left := @unzip_fst
@[deprecated unzip_snd (since := "2024-07-28")] abbrev unzip_right := @unzip_snd

theorem unzip_eq_map : ∀ l : List (α × β), unzip l = (l.map Prod.fst, l.map Prod.snd)
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, map_cons, unzip_eq_map l]

theorem zip_unzip : ∀ l : List (α × β), zip (unzip l).1 (unzip l).2 = l
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, zip_cons_cons, zip_unzip l]

theorem unzip_zip_left :
    ∀ {l₁ : List α} {l₂ : List β}, length l₁ ≤ length l₂ → (unzip (zip l₁ l₂)).1 = l₁
  | [], _, _ => rfl
  | _, [], h => by rw [eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)]; rfl
  | _ :: _, _ :: _, h => by
    simp only [zip_cons_cons, unzip_cons, unzip_zip_left (le_of_succ_le_succ h)]

theorem unzip_zip_right :
    ∀ {l₁ : List α} {l₂ : List β}, length l₂ ≤ length l₁ → (unzip (zip l₁ l₂)).2 = l₂
  | [], l₂, _ => by simp_all
  | l₁, [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [zip_cons_cons, unzip_cons, unzip_zip_right (le_of_succ_le_succ h)]

theorem unzip_zip {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  ext
  · rw [unzip_zip_left (Nat.le_of_eq h)]
  · rw [unzip_zip_right (Nat.le_of_eq h.symm)]

theorem zip_of_prod {l : List α} {l' : List β} {xs : List (α × β)} (hl : xs.map Prod.fst = l)
    (hr : xs.map Prod.snd = l') : xs = l.zip l' := by
  rw [← hl, ← hr, ← zip_unzip xs, ← unzip_fst, ← unzip_snd, zip_unzip, zip_unzip]

theorem tail_zip_fst {l : List (α × β)} : l.unzip.1.tail = l.tail.unzip.1 := by
  simp

theorem tail_zip_snd {l : List (α × β)} : l.unzip.2.tail = l.tail.unzip.2 := by
  simp

@[simp] theorem unzip_replicate {n : Nat} {a : α} {b : β} :
    unzip (replicate n (a, b)) = (replicate n a, replicate n b) := by
  ext1 <;> simp
