/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.TakeDrop
import Init.Data.List.Zip

/-!
# Lemmas about `Array.zip`, `Array.zipWith`, `Array.zipWithAll`, and `Array.unzip`.
-/

namespace Array

open Nat

/-! ## Zippers -/

/-! ### zipWith -/

theorem zipWith_comm (f : α → β → γ) (la : Array α) (lb : Array β) :
    zipWith f la lb = zipWith (fun b a => f a b) lb la := by
  cases la
  cases lb
  simpa using List.zipWith_comm _ _ _

theorem zipWith_comm_of_comm (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : Array α) :
    zipWith f l l' = zipWith f l' l := by
  rw [zipWith_comm]
  simp only [comm]

@[simp]
theorem zipWith_self (f : α → α → δ) (l : Array α) : zipWith f l l = l.map fun a => f a a := by
  cases l
  simp

/--
See also `getElem?_zipWith'` for a variant
using `Option.map` and `Option.bind` rather than a `match`.
-/
theorem getElem?_zipWith {f : α → β → γ} {i : Nat} :
    (zipWith f as bs)[i]? = match as[i]?, bs[i]? with
      | some a, some b => some (f a b) | _, _ => none := by
  cases as
  cases bs
  simp [List.getElem?_zipWith]
  rfl

/-- Variant of `getElem?_zipWith` using `Option.map` and `Option.bind` rather than a `match`. -/
theorem getElem?_zipWith' {f : α → β → γ} {i : Nat} :
    (zipWith f l₁ l₂)[i]? = (l₁[i]?.map f).bind fun g => l₂[i]?.map g := by
  cases l₁
  cases l₂
  simp [List.getElem?_zipWith']

theorem getElem?_zipWith_eq_some {f : α → β → γ} {l₁ : Array α} {l₂ : Array β} {z : γ} {i : Nat} :
    (zipWith f l₁ l₂)[i]? = some z ↔
      ∃ x y, l₁[i]? = some x ∧ l₂[i]? = some y ∧ f x y = z := by
  cases l₁
  cases l₂
  simp [List.getElem?_zipWith_eq_some]

theorem getElem?_zip_eq_some {l₁ : Array α} {l₂ : Array β} {z : α × β} {i : Nat} :
    (zip l₁ l₂)[i]? = some z ↔ l₁[i]? = some z.1 ∧ l₂[i]? = some z.2 := by
  cases z
  rw [zip, getElem?_zipWith_eq_some]; constructor
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    simpa [h₀, h₁] using h₂
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, _, h₀, h₁, rfl⟩

@[simp]
theorem zipWith_map {μ} (f : γ → δ → μ) (g : α → γ) (h : β → δ) (l₁ : Array α) (l₂ : Array β) :
    zipWith f (l₁.map g) (l₂.map h) = zipWith (fun a b => f (g a) (h b)) l₁ l₂ := by
  cases l₁
  cases l₂
  simp [List.zipWith_map]

theorem zipWith_map_left (l₁ : Array α) (l₂ : Array β) (f : α → α') (g : α' → β → γ) :
    zipWith g (l₁.map f) l₂ = zipWith (fun a b => g (f a) b) l₁ l₂ := by
  cases l₁
  cases l₂
  simp [List.zipWith_map_left]

theorem zipWith_map_right (l₁ : Array α) (l₂ : Array β) (f : β → β') (g : α → β' → γ) :
    zipWith g l₁ (l₂.map f) = zipWith (fun a b => g a (f b)) l₁ l₂ := by
  cases l₁
  cases l₂
  simp [List.zipWith_map_right]

theorem zipWith_foldr_eq_zip_foldr {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldr g i = (zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  cases l₁
  cases l₂
  simp [List.zipWith_foldr_eq_zip_foldr]

theorem zipWith_foldl_eq_zip_foldl {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldl g i = (zip l₁ l₂).foldl (fun r p => g r (f p.1 p.2)) i := by
  cases l₁
  cases l₂
  simp [List.zipWith_foldl_eq_zip_foldl]

@[simp]
theorem zipWith_eq_empty_iff {f : α → β → γ} {l l'} : zipWith f l l' = #[] ↔ l = #[] ∨ l' = #[] := by
  cases l <;> cases l' <;> simp

theorem map_zipWith {δ : Type _} (f : α → β) (g : γ → δ → α) (l : Array γ) (l' : Array δ) :
    map f (zipWith g l l') = zipWith (fun x y => f (g x y)) l l' := by
  cases l
  cases l'
  simp [List.map_zipWith]

theorem take_zipWith : (zipWith f l l').take n = zipWith f (l.take n) (l'.take n) := by
  cases l
  cases l'
  simp [List.take_zipWith]

theorem extract_zipWith : (zipWith f l l').extract m n = zipWith f (l.extract m n) (l'.extract m n) := by
  cases l
  cases l'
  simp [List.drop_zipWith, List.take_zipWith]

theorem zipWith_append (f : α → β → γ) (l la : Array α) (l' lb : Array β)
    (h : l.size = l'.size) :
    zipWith f (l ++ la) (l' ++ lb) = zipWith f l l' ++ zipWith f la lb := by
  cases l
  cases l'
  cases la
  cases lb
  simp at h
  simp [List.zipWith_append, h]

theorem zipWith_eq_append_iff {f : α → β → γ} {l₁ : Array α} {l₂ : Array β} :
    zipWith f l₁ l₂ = l₁' ++ l₂' ↔
      ∃ w x y z, w.size = y.size ∧ l₁ = w ++ x ∧ l₂ = y ++ z ∧ l₁' = zipWith f w y ∧ l₂' = zipWith f x z := by
  cases l₁
  cases l₂
  cases l₁'
  cases l₂'
  simp only [List.zipWith_toArray, List.append_toArray, mk.injEq, List.zipWith_eq_append_iff,
    toArray_eq_append_iff]
  constructor
  · rintro ⟨w, x, y, z, h, rfl, rfl, rfl, rfl⟩
    exact ⟨w.toArray, x.toArray, y.toArray, z.toArray, by simp [h]⟩
  · rintro ⟨⟨w⟩, ⟨x⟩, ⟨y⟩, ⟨z⟩, h, rfl, rfl, h₁, h₂⟩
    exact ⟨w, x, y, z, by simp_all⟩

@[simp] theorem zipWith_mkArray {a : α} {b : β} {m n : Nat} :
    zipWith f (mkArray m a) (mkArray n b) = mkArray (min m n) (f a b) := by
  simp [← List.toArray_replicate]

theorem map_uncurry_zip_eq_zipWith (f : α → β → γ) (l : Array α) (l' : Array β) :
    map (Function.uncurry f) (l.zip l') = zipWith f l l' := by
  cases l
  cases l'
  simp [List.map_uncurry_zip_eq_zipWith]

theorem map_zip_eq_zipWith (f : α × β → γ) (l : Array α) (l' : Array β) :
    map f (l.zip l') = zipWith (Function.curry f) l l' := by
  cases l
  cases l'
  simp [List.map_zip_eq_zipWith]

theorem lt_size_left_of_zipWith {f : α → β → γ} {i : Nat} {l : Array α} {l' : Array β}
    (h : i < (zipWith f l l').size) : i < l.size := by rw [size_zipWith] at h; omega

theorem lt_size_right_of_zipWith {f : α → β → γ} {i : Nat} {l : Array α} {l' : Array β}
    (h : i < (zipWith f l l').size) : i < l'.size := by rw [size_zipWith] at h; omega

theorem zipWith_eq_zipWith_take_min (l₁ : Array α) (l₂ : Array β) :
    zipWith f l₁ l₂ = zipWith f (l₁.take (min l₁.size l₂.size)) (l₂.take (min l₁.size l₂.size)) := by
  cases l₁
  cases l₂
  simp
  rw [List.zipWith_eq_zipWith_take_min]

theorem reverse_zipWith (h : l.size = l'.size) :
    (zipWith f l l').reverse = zipWith f l.reverse l'.reverse := by
  cases l
  cases l'
  simp [List.reverse_zipWith (by simpa using h)]

/-! ### zip -/

theorem lt_size_left_of_zip {i : Nat} {l : Array α} {l' : Array β} (h : i < (zip l l').size) :
    i < l.size :=
  lt_size_left_of_zipWith h

theorem lt_size_right_of_zip {i : Nat} {l : Array α} {l' : Array β} (h : i < (zip l l').size) :
    i < l'.size :=
  lt_size_right_of_zipWith h

@[simp]
theorem getElem_zip {l : Array α} {l' : Array β} {i : Nat} {h : i < (zip l l').size} :
    (zip l l')[i] =
      (l[i]'(lt_size_left_of_zip h), l'[i]'(lt_size_right_of_zip h)) :=
  getElem_zipWith (hi := by simpa using h)

theorem zip_eq_zipWith (l₁ : Array α) (l₂ : Array β) : zip l₁ l₂ = zipWith Prod.mk l₁ l₂ := by
  cases l₁
  cases l₂
  simp [List.zip_eq_zipWith]

theorem zip_map (f : α → γ) (g : β → δ) (l₁ : Array α) (l₂ : Array β) :
    zip (l₁.map f) (l₂.map g) = (zip l₁ l₂).map (Prod.map f g) := by
  cases l₁
  cases l₂
  simp [List.zip_map]

theorem zip_map_left (f : α → γ) (l₁ : Array α) (l₂ : Array β) :
    zip (l₁.map f) l₂ = (zip l₁ l₂).map (Prod.map f id) := by rw [← zip_map, map_id]

theorem zip_map_right (f : β → γ) (l₁ : Array α) (l₂ : Array β) :
    zip l₁ (l₂.map f) = (zip l₁ l₂).map (Prod.map id f) := by rw [← zip_map, map_id]

theorem zip_append {l₁ r₁ : Array α} {l₂ r₂ : Array β} (_h : l₁.size = l₂.size) :
    zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂ := by
  cases l₁
  cases l₂
  cases r₁
  cases r₂
  simp_all [List.zip_append]

theorem zip_map' (f : α → β) (g : α → γ) (l : Array α) :
    zip (l.map f) (l.map g) = l.map fun a => (f a, g a) := by
  cases l
  simp [List.zip_map']

theorem of_mem_zip {a b} {l₁ : Array α} {l₂ : Array β} : (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂ := by
  cases l₁
  cases l₂
  simpa using List.of_mem_zip

theorem map_fst_zip (l₁ : Array α) (l₂ : Array β) (h : l₁.size ≤ l₂.size) :
    map Prod.fst (zip l₁ l₂) = l₁ := by
  cases l₁
  cases l₂
  simp_all [List.map_fst_zip]

theorem map_snd_zip (l₁ : Array α) (l₂ : Array β) (h : l₂.size ≤ l₁.size) :
    map Prod.snd (zip l₁ l₂) = l₂ := by
  cases l₁
  cases l₂
  simp_all [List.map_snd_zip]

theorem map_prod_left_eq_zip {l : Array α} (f : α → β) :
    (l.map fun x => (x, f x)) = l.zip (l.map f) := by
  rw [← zip_map']
  congr
  simp

theorem map_prod_right_eq_zip {l : Array α} (f : α → β) :
    (l.map fun x => (f x, x)) = (l.map f).zip l := by
  rw [← zip_map']
  congr
  simp

@[simp] theorem zip_eq_empty_iff {l₁ : Array α} {l₂ : Array β} :
    zip l₁ l₂ = #[] ↔ l₁ = #[] ∨ l₂ = #[] := by
  cases l₁
  cases l₂
  simp [List.zip_eq_nil_iff]

theorem zip_eq_append_iff {l₁ : Array α} {l₂ : Array β} :
    zip l₁ l₂ = l₁' ++ l₂' ↔
      ∃ w x y z, w.size = y.size ∧ l₁ = w ++ x ∧ l₂ = y ++ z ∧ l₁' = zip w y ∧ l₂' = zip x z := by
  simp [zip_eq_zipWith, zipWith_eq_append_iff]

@[simp] theorem zip_mkArray {a : α} {b : β} {m n : Nat} :
    zip (mkArray m a) (mkArray n b) = mkArray (min m n) (a, b) := by
  simp [← List.toArray_replicate]

theorem zip_eq_zip_take_min (l₁ : Array α) (l₂ : Array β) :
    zip l₁ l₂ = zip (l₁.take (min l₁.size l₂.size)) (l₂.take (min l₁.size l₂.size)) := by
  cases l₁
  cases l₂
  simp only [List.zip_toArray, List.size_toArray, List.take_toArray, mk.injEq]
  rw [List.zip_eq_zip_take_min]


/-! ### zipWithAll -/

theorem getElem?_zipWithAll {f : Option α → Option β → γ} {i : Nat} :
    (zipWithAll f as bs)[i]? = match as[i]?, bs[i]? with
      | none, none => .none | a?, b? => some (f a? b?) := by
  cases as
  cases bs
  simp [List.getElem?_zipWithAll]
  rfl

theorem zipWithAll_map {μ} (f : Option γ → Option δ → μ) (g : α → γ) (h : β → δ) (l₁ : Array α) (l₂ : Array β) :
    zipWithAll f (l₁.map g) (l₂.map h) = zipWithAll (fun a b => f (g <$> a) (h <$> b)) l₁ l₂ := by
  cases l₁
  cases l₂
  simp [List.zipWithAll_map]

theorem zipWithAll_map_left (l₁ : Array α) (l₂ : Array β) (f : α → α') (g : Option α' → Option β → γ) :
    zipWithAll g (l₁.map f) l₂ = zipWithAll (fun a b => g (f <$> a) b) l₁ l₂ := by
  cases l₁
  cases l₂
  simp [List.zipWithAll_map_left]

theorem zipWithAll_map_right (l₁ : Array α) (l₂ : Array β) (f : β → β') (g : Option α → Option β' → γ) :
    zipWithAll g l₁ (l₂.map f) = zipWithAll (fun a b => g a (f <$> b)) l₁ l₂ := by
  cases l₁
  cases l₂
  simp [List.zipWithAll_map_right]

theorem map_zipWithAll {δ : Type _} (f : α → β) (g : Option γ → Option δ → α) (l : Array γ) (l' : Array δ) :
    map f (zipWithAll g l l') = zipWithAll (fun x y => f (g x y)) l l' := by
  cases l
  cases l'
  simp [List.map_zipWithAll]


@[simp] theorem zipWithAll_replicate {a : α} {b : β} {n : Nat} :
    zipWithAll f (mkArray n a) (mkArray n b) = mkArray n (f a b) := by
  simp [← List.toArray_replicate]

/-! ### unzip -/

@[simp] theorem unzip_fst : (unzip l).fst = l.map Prod.fst := by
  induction l <;> simp_all

@[simp] theorem unzip_snd : (unzip l).snd = l.map Prod.snd := by
  induction l <;> simp_all

theorem unzip_eq_map (l : Array (α × β)) : unzip l = (l.map Prod.fst, l.map Prod.snd) := by
  cases l
  simp [List.unzip_eq_map]

theorem zip_unzip (l : Array (α × β)) : zip (unzip l).1 (unzip l).2 = l := by
  cases l
  simp only [List.unzip_toArray, Prod.map_fst, Prod.map_snd, List.zip_toArray, List.zip_unzip]

theorem unzip_zip_left {l₁ : Array α} {l₂ : Array β} (h : l₁.size ≤ l₂.size) :
    (unzip (zip l₁ l₂)).1 = l₁ := by
  cases l₁
  cases l₂
  simp_all only [List.size_toArray, List.zip_toArray, List.unzip_toArray, Prod.map_fst,
    List.unzip_zip_left]

theorem unzip_zip_right {l₁ : Array α} {l₂ : Array β} (h : l₂.size ≤ l₁.size) :
    (unzip (zip l₁ l₂)).2 = l₂ := by
  cases l₁
  cases l₂
  simp_all only [List.size_toArray, List.zip_toArray, List.unzip_toArray, Prod.map_snd,
    List.unzip_zip_right]

theorem unzip_zip {l₁ : Array α} {l₂ : Array β} (h : l₁.size = l₂.size) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  cases l₁
  cases l₂
  simp_all only [List.size_toArray, List.zip_toArray, List.unzip_toArray, List.unzip_zip, Prod.map_apply]

theorem zip_of_prod {l : Array α} {l' : Array β} {lp : Array (α × β)} (hl : lp.map Prod.fst = l)
    (hr : lp.map Prod.snd = l') : lp = l.zip l' := by
  rw [← hl, ← hr, ← zip_unzip lp, ← unzip_fst, ← unzip_snd, zip_unzip, zip_unzip]

@[simp] theorem unzip_mkArray {n : Nat} {a : α} {b : β} :
    unzip (mkArray n (a, b)) = (mkArray n a, mkArray n b) := by
  ext1 <;> simp
