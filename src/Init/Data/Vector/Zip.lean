/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import all Init.Data.Array.Basic
import Init.Data.Array.Zip
import all Init.Data.Vector.Basic
import Init.Data.Vector.Lemmas

/-!
# Lemmas about `Vector.zip`, `Vector.zipWith`, `Vector.zipWithAll`, and `Vector.unzip`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

open Nat

/-! ## Zippers -/

/-! ### zipWith -/

theorem zipWith_comm {f : α → β → γ} {as : Vector α n} {bs : Vector β n} :
    zipWith f as bs = zipWith (fun b a => f a b) bs as := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simpa using Array.zipWith_comm

theorem zipWith_comm_of_comm {f : α → α → β} (comm : ∀ x y : α, f x y = f y x) {xs ys : Vector α n} :
    zipWith f xs ys = zipWith f ys xs := by
  rw [zipWith_comm]
  simp only [comm]

@[simp]
theorem zipWith_self {f : α → α → δ} {xs : Vector α n} : zipWith f xs xs = xs.map fun a => f a a := by
  cases xs
  simp

/--
See also `getElem?_zipWith'` for a variant
using `Option.map` and `Option.bind` rather than a `match`.
-/
@[grind =]
theorem getElem?_zipWith {f : α → β → γ} {i : Nat} :
    (zipWith f as bs)[i]? = match as[i]?, bs[i]? with
      | some a, some b => some (f a b) | _, _ => none := by
  cases as
  cases bs
  simp [Array.getElem?_zipWith]
  rfl

/-- Variant of `getElem?_zipWith` using `Option.map` and `Option.bind` rather than a `match`. -/
theorem getElem?_zipWith' {f : α → β → γ} {i : Nat} :
    (zipWith f as bs)[i]? = (as[i]?.map f).bind fun g => bs[i]?.map g := by
  cases as
  cases bs
  simp [Array.getElem?_zipWith']

theorem getElem?_zipWith_eq_some {f : α → β → γ} {as : Vector α n} {bs : Vector β n} {z : γ} {i : Nat} :
    (zipWith f as bs)[i]? = some z ↔
      ∃ x y, as[i]? = some x ∧ bs[i]? = some y ∧ f x y = z := by
  cases as
  cases bs
  simp [Array.getElem?_zipWith_eq_some]

theorem getElem?_zip_eq_some {as : Vector α n} {bs : Vector β n} {z : α × β} {i : Nat} :
    (zip as bs)[i]? = some z ↔ as[i]? = some z.1 ∧ bs[i]? = some z.2 := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.getElem?_zip_eq_some]

@[simp, grind =]
theorem zipWith_map {μ} {f : γ → δ → μ} {g : α → γ} {h : β → δ} {as : Vector α n} {bs : Vector β n} :
    zipWith f (as.map g) (bs.map h) = zipWith (fun a b => f (g a) (h b)) as bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.zipWith_map]

@[grind =]
theorem zipWith_map_left {as : Vector α n} {bs : Vector β n} {f : α → α'} {g : α' → β → γ} :
    zipWith g (as.map f) bs = zipWith (fun a b => g (f a) b) as bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.zipWith_map_left]

@[grind =]
theorem zipWith_map_right {as : Vector α n} {bs : Vector β n} {f : β → β'} {g : α → β' → γ} :
    zipWith g as (bs.map f) = zipWith (fun a b => g a (f b)) as bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.zipWith_map_right]

@[grind =]
theorem zipWith_foldr_eq_zip_foldr {f : α → β → γ} {i : δ} :
    (zipWith f as bs).foldr g i = (zip as bs).foldr (fun p r => g (f p.1 p.2) r) i := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simpa using Array.zipWith_foldr_eq_zip_foldr

@[grind =]
theorem zipWith_foldl_eq_zip_foldl {f : α → β → γ} {i : δ} :
    (zipWith f as bs).foldl g i = (zip as bs).foldl (fun r p => g r (f p.1 p.2)) i := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simpa using Array.zipWith_foldl_eq_zip_foldl

@[grind =]
theorem map_zipWith {δ : Type _} {f : α → β} {g : γ → δ → α} {as : Vector γ n} {bs : Vector δ n} :
    map f (zipWith g as bs) = zipWith (fun x y => f (g x y)) as bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.map_zipWith]

@[grind =]
theorem take_zipWith : (zipWith f as bs).take i = zipWith f (as.take i) (bs.take i) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.take_zipWith]

@[grind =]
theorem extract_zipWith : (zipWith f as bs).extract i j = zipWith f (as.extract i j) (bs.extract i j) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.extract_zipWith]

@[grind =]
theorem zipWith_append {f : α → β → γ}
    {as : Vector α n} {as' : Vector α m} {bs : Vector β n} {bs' : Vector β m} :
    zipWith f (as ++ as') (bs ++ bs') = zipWith f as bs ++ zipWith f as' bs' := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  rcases as' with ⟨as', rfl⟩
  rcases bs' with ⟨bs', h'⟩
  simp [Array.zipWith_append, *]

theorem zipWith_eq_append_iff {f : α → β → γ} {as : Vector α (n + m)} {bs : Vector β (n + m)} :
    zipWith f as bs = xs ++ ys ↔
      ∃ as₁ as₂ bs₁ bs₂, as = as₁ ++ as₂ ∧ bs = bs₁ ++ bs₂ ∧ xs = zipWith f as₁ bs₁ ∧ ys = zipWith f as₂ bs₂ := by
  rcases as with ⟨as, h₁⟩
  rcases bs with ⟨bs, h₂⟩
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [mk_zipWith_mk, mk_append_mk, eq_mk, Array.zipWith_eq_append_iff,
    mk_eq, toArray_append, toArray_zipWith]
  constructor
  · rintro ⟨as₁, as₂, bs₁, bs₂, h, rfl, rfl, rfl, rfl⟩
    simp only [Array.size_append, Array.size_zipWith] at h₁ h₂
    exact ⟨mk as₁ (by simp; omega), mk as₂ (by simp; omega), mk bs₁ (by simp; omega), mk bs₂ (by simp; omega), by simp⟩
  · rintro ⟨⟨as₁, hw⟩, ⟨as₂, hx⟩, ⟨bs₁, hy⟩, ⟨bs₂, hz⟩, rfl, rfl, w₁, w₂⟩
    simp only at w₁ w₂
    exact ⟨as₁, as₂, bs₁, bs₂, by simpa [hw, hy] using ⟨w₁, w₂⟩⟩

@[simp, grind =]
theorem zipWith_replicate {a : α} {b : β} {n : Nat} :
    zipWith f (replicate n a) (replicate n b) = replicate n (f a b) := by
  ext
  simp

@[deprecated zipWith_replicate (since := "2025-03-18")]
abbrev zipWith_mkVector := @zipWith_replicate

theorem map_uncurry_zip_eq_zipWith {f : α → β → γ} {as : Vector α n} {bs : Vector β n} :
    map (Function.uncurry f) (as.zip bs) = zipWith f as bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.map_uncurry_zip_eq_zipWith]

theorem map_zip_eq_zipWith {f : α × β → γ} {as : Vector α n} {bs : Vector β n} :
    map f (as.zip bs) = zipWith (Function.curry f) as bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.map_zip_eq_zipWith]

@[grind =]
theorem reverse_zipWith {f : α → β → γ} {as : Vector α n} {bs : Vector β n} :
    (zipWith f as bs).reverse = zipWith f as.reverse bs.reverse := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.reverse_zipWith, h]

/-! ### zip -/

@[simp, grind =]
theorem getElem_zip {as : Vector α n} {bs : Vector β n} {i : Nat} {h : i < n} :
    (zip as bs)[i] = (as[i], bs[i]) :=
  getElem_zipWith ..

theorem zip_eq_zipWith {as : Vector α n} {bs : Vector β n} : zip as bs = zipWith Prod.mk as bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.zip_eq_zipWith, h]

@[grind _=_]
theorem zip_map {f : α → γ} {g : β → δ} {as : Vector α n} {bs : Vector β n} :
    zip (as.map f) (bs.map g) = (zip as bs).map (Prod.map f g) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.zip_map, h]

@[grind _=_]
theorem zip_map_left {f : α → γ} {as : Vector α n} {bs : Vector β n} :
    zip (as.map f) bs = (zip as bs).map (Prod.map f id) := by rw [← zip_map, map_id]

@[grind _=_]
theorem zip_map_right {f : β → γ} {as : Vector α n} {bs : Vector β n} :
    zip as (bs.map f) = (zip as bs).map (Prod.map id f) := by rw [← zip_map, map_id]

@[grind =]
theorem zip_append {as : Vector α n} {bs : Vector β n} {as' : Vector α m} {bs' : Vector β m} :
    zip (as ++ as') (bs ++ bs') = zip as bs ++ zip as' bs' := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  rcases as' with ⟨as', rfl⟩
  rcases bs' with ⟨bs', h'⟩
  simp [Array.zip_append, h, h']

@[grind =]
theorem zip_map' {f : α → β} {g : α → γ} {xs : Vector α n} :
    zip (xs.map f) (xs.map g) = xs.map fun a => (f a, g a) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.zip_map']

theorem of_mem_zip {a b} {as : Vector α n} {bs : Vector β n} : (a, b) ∈ zip as bs → a ∈ as ∧ b ∈ bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simpa using Array.of_mem_zip

-- The argument `as` is explicit so we can rewrite from right to left.
theorem map_fst_zip (as : Vector α n) {bs : Vector β n} :
    map Prod.fst (zip as bs) = as := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.map_fst_zip, h]

-- The argument `bs` is explicit so we can rewrite from right to left.
theorem map_snd_zip {as : Vector α n} (bs : Vector β n) :
    map Prod.snd (zip as bs) = bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.map_snd_zip, h]

theorem map_prod_left_eq_zip {xs : Vector α n} {f : α → β} :
    (xs.map fun x => (x, f x)) = xs.zip (xs.map f) := by
  rcases xs with ⟨xs, rfl⟩
  rw [← zip_map']
  congr
  simp

theorem map_prod_right_eq_zip {xs : Vector α n} {f : α → β} :
    (xs.map fun x => (f x, x)) = (xs.map f).zip xs := by
  rcases xs with ⟨xs, rfl⟩
  rw [← zip_map']
  congr
  simp

theorem zip_eq_append_iff {as : Vector α (n + m)} {bs : Vector β (n + m)} {xs : Vector (α × β) n} {ys : Vector (α × β) m} :
    zip as bs = xs ++ ys ↔
      ∃ as₁ as₂ bs₁ bs₂, as = as₁ ++ as₂ ∧ bs = bs₁ ++ bs₂ ∧ xs = zip as₁ bs₁ ∧ ys = zip as₂ bs₂ := by
  simp [zip_eq_zipWith, zipWith_eq_append_iff]

@[simp, grind =]
theorem zip_replicate {a : α} {b : β} {n : Nat} :
    zip (replicate n a) (replicate n b) = replicate n (a, b) := by
  ext <;> simp

@[deprecated zip_replicate (since := "2025-03-18")]
abbrev zip_mkVector := @zip_replicate

/-! ### unzip -/

@[simp, grind =]
theorem unzip_fst : (unzip xs).fst = xs.map Prod.fst := by
  cases xs
  simp_all

@[simp, grind =]
theorem unzip_snd : (unzip xs).snd = xs.map Prod.snd := by
  cases xs
  simp_all

@[grind =]
theorem unzip_eq_map {xs : Vector (α × β) n} : unzip xs = (xs.map Prod.fst, xs.map Prod.snd) := by
  cases xs
  simp [List.unzip_eq_map]

-- The argument `xs` is explicit so we can rewrite from right to left.
theorem zip_unzip (xs : Vector (α × β) n) : zip (unzip xs).1 (unzip xs).2 = xs := by
  cases xs
  simp only [unzip_mk, mk_zip_mk, Array.zip_unzip]

theorem unzip_zip_left {as : Vector α n} {bs : Vector β n}  :
    (unzip (zip as bs)).1 = as := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.unzip_zip_left, h, Array.map_fst_zip]

theorem unzip_zip_right {as : Vector α n} {bs : Vector β n} :
    (unzip (zip as bs)).2 = bs := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.unzip_zip_right, h, Array.map_snd_zip]

theorem unzip_zip {as : Vector α n} {bs : Vector β n} :
    unzip (zip as bs) = (as, bs) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h⟩
  simp [Array.unzip_zip, h, Array.map_fst_zip, Array.map_snd_zip]

theorem zip_of_prod {as : Vector α n} {bs : Vector β n} {xs : Vector (α × β) n} (hl : xs.map Prod.fst = as)
    (hr : xs.map Prod.snd = bs) : xs = as.zip bs := by
  rw [← hl, ← hr, ← zip_unzip xs, ← unzip_fst, ← unzip_snd, zip_unzip, zip_unzip]

@[simp, grind =]
theorem unzip_replicate {a : α} {b : β} {n : Nat} :
    unzip (replicate n (a, b)) = (replicate n a, replicate n b) := by
  ext1 <;> simp

@[deprecated unzip_replicate (since := "2025-03-18")]
abbrev unzip_mkVector := @unzip_replicate

end Vector
