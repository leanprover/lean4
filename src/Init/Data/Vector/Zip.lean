/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Zip
import Init.Data.Vector.Lemmas

/-!
# Lemmas about `Vector.zip`, `Vector.zipWith`, `Vector.zipWithAll`, and `Vector.unzip`.
-/

namespace Vector

open Nat

/-! ## Zippers -/

/-! ### zipWith -/

theorem zipWith_comm (f : α → β → γ) (la : Vector α n) (lb : Vector β n) :
    zipWith f la lb = zipWith (fun b a => f a b) lb la := by
  rcases la with ⟨la, rfl⟩
  rcases lb with ⟨lb, h⟩
  simpa using Array.zipWith_comm _ _ _

theorem zipWith_comm_of_comm (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : Vector α n) :
    zipWith f l l' = zipWith f l' l := by
  rw [zipWith_comm]
  simp only [comm]

@[simp]
theorem zipWith_self (f : α → α → δ) (l : Vector α n) : zipWith f l l = l.map fun a => f a a := by
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
  simp [Array.getElem?_zipWith]
  rfl

/-- Variant of `getElem?_zipWith` using `Option.map` and `Option.bind` rather than a `match`. -/
theorem getElem?_zipWith' {f : α → β → γ} {i : Nat} :
    (zipWith f l₁ l₂)[i]? = (l₁[i]?.map f).bind fun g => l₂[i]?.map g := by
  cases l₁
  cases l₂
  simp [Array.getElem?_zipWith']

theorem getElem?_zipWith_eq_some {f : α → β → γ} {l₁ : Vector α n} {l₂ : Vector β n} {z : γ} {i : Nat} :
    (zipWith f l₁ l₂)[i]? = some z ↔
      ∃ x y, l₁[i]? = some x ∧ l₂[i]? = some y ∧ f x y = z := by
  cases l₁
  cases l₂
  simp [Array.getElem?_zipWith_eq_some]

theorem getElem?_zip_eq_some {l₁ : Vector α n} {l₂ : Vector β n} {z : α × β} {i : Nat} :
    (zip l₁ l₂)[i]? = some z ↔ l₁[i]? = some z.1 ∧ l₂[i]? = some z.2 := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.getElem?_zip_eq_some]

@[simp]
theorem zipWith_map {μ} (f : γ → δ → μ) (g : α → γ) (h : β → δ) (l₁ : Vector α n) (l₂ : Vector β n) :
    zipWith f (l₁.map g) (l₂.map h) = zipWith (fun a b => f (g a) (h b)) l₁ l₂ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.zipWith_map]

theorem zipWith_map_left (l₁ : Vector α n) (l₂ : Vector β n) (f : α → α') (g : α' → β → γ) :
    zipWith g (l₁.map f) l₂ = zipWith (fun a b => g (f a) b) l₁ l₂ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.zipWith_map_left]

theorem zipWith_map_right (l₁ : Vector α n) (l₂ : Vector β n) (f : β → β') (g : α → β' → γ) :
    zipWith g l₁ (l₂.map f) = zipWith (fun a b => g a (f b)) l₁ l₂ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.zipWith_map_right]

theorem zipWith_foldr_eq_zip_foldr {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldr g i = (zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simpa using Array.zipWith_foldr_eq_zip_foldr _

theorem zipWith_foldl_eq_zip_foldl {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldl g i = (zip l₁ l₂).foldl (fun r p => g r (f p.1 p.2)) i := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simpa using Array.zipWith_foldl_eq_zip_foldl _


theorem map_zipWith {δ : Type _} (f : α → β) (g : γ → δ → α) (l : Vector γ n) (l' : Vector δ n) :
    map f (zipWith g l l') = zipWith (fun x y => f (g x y)) l l' := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h⟩
  simp [Array.map_zipWith]

theorem take_zipWith : (zipWith f l l').take n = zipWith f (l.take n) (l'.take n) := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h⟩
  simp [Array.take_zipWith]

theorem extract_zipWith : (zipWith f l l').extract m n = zipWith f (l.extract m n) (l'.extract m n) := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h⟩
  simp [Array.extract_zipWith]

theorem zipWith_append (f : α → β → γ)
    (l : Vector α n) (la : Vector α m) (l' : Vector β n) (lb : Vector β m) :
    zipWith f (l ++ la) (l' ++ lb) = zipWith f l l' ++ zipWith f la lb := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h⟩
  rcases la with ⟨la, rfl⟩
  rcases lb with ⟨lb, h'⟩
  simp [Array.zipWith_append, *]

theorem zipWith_eq_append_iff {f : α → β → γ} {l₁ : Vector α (n + m)} {l₂ : Vector β (n + m)} :
    zipWith f l₁ l₂ = l₁' ++ l₂' ↔
      ∃ w x y z, l₁ = w ++ x ∧ l₂ = y ++ z ∧ l₁' = zipWith f w y ∧ l₂' = zipWith f x z := by
  rcases l₁ with ⟨l₁, h₁⟩
  rcases l₂ with ⟨l₂, h₂⟩
  rcases l₁' with ⟨l₁', rfl⟩
  rcases l₂' with ⟨l₂', rfl⟩
  simp only [mk_zipWith_mk, mk_append_mk, eq_mk, Array.zipWith_eq_append_iff,
    mk_eq, toArray_append, toArray_zipWith]
  constructor
  · rintro ⟨w, x, y, z, h, rfl, rfl, rfl, rfl⟩
    simp only [Array.size_append, Array.size_zipWith] at h₁ h₂
    exact ⟨mk w (by simp; omega), mk x (by simp; omega), mk y (by simp; omega), mk z (by simp; omega), by simp⟩
  · rintro ⟨⟨w, hw⟩, ⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, rfl, rfl, w₁, w₂⟩
    simp only at w₁ w₂
    exact ⟨w, x, y, z, by simpa [hw, hy] using ⟨w₁, w₂⟩⟩

@[simp] theorem zipWith_mkVector {a : α} {b : β} {n : Nat} :
    zipWith f (mkVector n a) (mkVector n b) = mkVector n (f a b) := by
  ext
  simp

theorem map_uncurry_zip_eq_zipWith (f : α → β → γ) (l : Vector α n) (l' : Vector β n) :
    map (Function.uncurry f) (l.zip l') = zipWith f l l' := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h⟩
  simp [Array.map_uncurry_zip_eq_zipWith]

theorem map_zip_eq_zipWith (f : α × β → γ) (l : Vector α n) (l' : Vector β n) :
    map f (l.zip l') = zipWith (Function.curry f) l l' := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h⟩
  simp [Array.map_zip_eq_zipWith]

theorem reverse_zipWith :
    (zipWith f l l').reverse = zipWith f l.reverse l'.reverse := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h⟩
  simp [Array.reverse_zipWith, h]

/-! ### zip -/

@[simp]
theorem getElem_zip {l : Vector α n} {l' : Vector β n} {i : Nat} {h : i < n} :
    (zip l l')[i] = (l[i], l'[i]) :=
  getElem_zipWith ..

theorem zip_eq_zipWith (l₁ : Vector α n) (l₂ : Vector β n) : zip l₁ l₂ = zipWith Prod.mk l₁ l₂ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.zip_eq_zipWith, h]

theorem zip_map (f : α → γ) (g : β → δ) (l₁ : Vector α n) (l₂ : Vector β n) :
    zip (l₁.map f) (l₂.map g) = (zip l₁ l₂).map (Prod.map f g) := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.zip_map, h]

theorem zip_map_left (f : α → γ) (l₁ : Vector α n) (l₂ : Vector β n) :
    zip (l₁.map f) l₂ = (zip l₁ l₂).map (Prod.map f id) := by rw [← zip_map, map_id]

theorem zip_map_right (f : β → γ) (l₁ : Vector α n) (l₂ : Vector β n) :
    zip l₁ (l₂.map f) = (zip l₁ l₂).map (Prod.map id f) := by rw [← zip_map, map_id]

theorem zip_append {l₁ : Vector α n} {l₂ : Vector β n} {r₁ : Vector α m} {r₂ : Vector β m} :
    zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  rcases r₁ with ⟨r₁, rfl⟩
  rcases r₂ with ⟨r₂, h'⟩
  simp [Array.zip_append, h, h']

theorem zip_map' (f : α → β) (g : α → γ) (l : Vector α n) :
    zip (l.map f) (l.map g) = l.map fun a => (f a, g a) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.zip_map']

theorem of_mem_zip {a b} {l₁ : Vector α n} {l₂ : Vector β n} : (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simpa using Array.of_mem_zip

theorem map_fst_zip (l₁ : Vector α n) (l₂ : Vector β n) :
    map Prod.fst (zip l₁ l₂) = l₁ := by
  cases l₁
  cases l₂
  simp_all [Array.map_fst_zip]

theorem map_snd_zip (l₁ : Vector α n) (l₂ : Vector β n) :
    map Prod.snd (zip l₁ l₂) = l₂ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.map_snd_zip, h]

theorem map_prod_left_eq_zip {l : Vector α n} (f : α → β) :
    (l.map fun x => (x, f x)) = l.zip (l.map f) := by
  rcases l with ⟨l, rfl⟩
  rw [← zip_map']
  congr
  simp

theorem map_prod_right_eq_zip {l : Vector α n} (f : α → β) :
    (l.map fun x => (f x, x)) = (l.map f).zip l := by
  rcases l with ⟨l, rfl⟩
  rw [← zip_map']
  congr
  simp

theorem zip_eq_append_iff {l₁ : Vector α (n + m)} {l₂ : Vector β (n + m)} {l₁' : Vector (α × β) n} {l₂' : Vector (α × β) m} :
    zip l₁ l₂ = l₁' ++ l₂' ↔
      ∃ w x y z, l₁ = w ++ x ∧ l₂ = y ++ z ∧ l₁' = zip w y ∧ l₂' = zip x z := by
  simp [zip_eq_zipWith, zipWith_eq_append_iff]

@[simp] theorem zip_mkVector {a : α} {b : β} {n : Nat} :
    zip (mkVector n a) (mkVector n b) = mkVector n (a, b) := by
  ext <;> simp


/-! ### unzip -/

@[simp] theorem unzip_fst : (unzip l).fst = l.map Prod.fst := by
  induction l <;> simp_all

@[simp] theorem unzip_snd : (unzip l).snd = l.map Prod.snd := by
  induction l <;> simp_all

theorem unzip_eq_map (l : Vector (α × β) n) : unzip l = (l.map Prod.fst, l.map Prod.snd) := by
  cases l
  simp [List.unzip_eq_map]

theorem zip_unzip (l : Vector (α × β) n) : zip (unzip l).1 (unzip l).2 = l := by
  rcases l with ⟨l, rfl⟩
  simp only [unzip_mk, mk_zip_mk, Array.zip_unzip]

theorem unzip_zip_left {l₁ : Vector α n} {l₂ : Vector β n}  :
    (unzip (zip l₁ l₂)).1 = l₁ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.unzip_zip_left, h, Array.map_fst_zip]

theorem unzip_zip_right {l₁ : Vector α n} {l₂ : Vector β n} :
    (unzip (zip l₁ l₂)).2 = l₂ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.unzip_zip_right, h, Array.map_snd_zip]

theorem unzip_zip {l₁ : Vector α n} {l₂ : Vector β n} :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, h⟩
  simp [Array.unzip_zip, h, Array.map_fst_zip, Array.map_snd_zip]

theorem zip_of_prod {l : Vector α n} {l' : Vector β n} {lp : Vector (α × β) n} (hl : lp.map Prod.fst = l)
    (hr : lp.map Prod.snd = l') : lp = l.zip l' := by
  rw [← hl, ← hr, ← zip_unzip lp, ← unzip_fst, ← unzip_snd, zip_unzip, zip_unzip]

@[simp] theorem unzip_mkVector {n : Nat} {a : α} {b : β} :
    unzip (mkVector n (a, b)) = (mkVector n a, mkVector n b) := by
  ext1 <;> simp

end Vector
