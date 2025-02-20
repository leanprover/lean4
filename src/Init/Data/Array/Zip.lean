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

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

open Nat

/-! ## Zippers -/

/-! ### zipWith -/

theorem zipWith_comm (f : α → β → γ) (as : Array α) (bs : Array β) :
    zipWith f as bs = zipWith (fun b a => f a b) bs as := by
  cases as
  cases bs
  simpa using List.zipWith_comm _ _ _

theorem zipWith_comm_of_comm (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (xs ys : Array α) :
    zipWith f xs ys = zipWith f ys xs := by
  rw [zipWith_comm]
  simp only [comm]

@[simp]
theorem zipWith_self (f : α → α → δ) (xs : Array α) : zipWith f xs xs = xs.map fun a => f a a := by
  cases xs
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

theorem getElem?_zipWith_eq_some {f : α → β → γ} {as : Array α} {bs : Array β} {z : γ} {i : Nat} :
    (zipWith f as bs)[i]? = some z ↔
      ∃ x y, as[i]? = some x ∧ bs[i]? = some y ∧ f x y = z := by
  cases as
  cases bs
  simp [List.getElem?_zipWith_eq_some]

theorem getElem?_zip_eq_some {as : Array α} {bs : Array β} {z : α × β} {i : Nat} :
    (zip as bs)[i]? = some z ↔ as[i]? = some z.1 ∧ bs[i]? = some z.2 := by
  cases z
  rw [zip, getElem?_zipWith_eq_some]; constructor
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    simpa [h₀, h₁] using h₂
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, _, h₀, h₁, rfl⟩

@[simp]
theorem zipWith_map {μ} (f : γ → δ → μ) (g : α → γ) (h : β → δ) (as : Array α) (bs : Array β) :
    zipWith f (as.map g) (bs.map h) = zipWith (fun a b => f (g a) (h b)) as bs := by
  cases as
  cases bs
  simp [List.zipWith_map]

theorem zipWith_map_left (as : Array α) (bs : Array β) (f : α → α') (g : α' → β → γ) :
    zipWith g (as.map f) bs = zipWith (fun a b => g (f a) b) as bs := by
  cases as
  cases bs
  simp [List.zipWith_map_left]

theorem zipWith_map_right (as : Array α) (bs : Array β) (f : β → β') (g : α → β' → γ) :
    zipWith g as (bs.map f) = zipWith (fun a b => g a (f b)) as bs := by
  cases as
  cases bs
  simp [List.zipWith_map_right]

theorem zipWith_foldr_eq_zip_foldr {f : α → β → γ} (i : δ):
    (zipWith f as bs).foldr g i = (zip as bs).foldr (fun p r => g (f p.1 p.2) r) i := by
  cases as
  cases bs
  simp [List.zipWith_foldr_eq_zip_foldr]

theorem zipWith_foldl_eq_zip_foldl {f : α → β → γ} (i : δ):
    (zipWith f as bs).foldl g i = (zip as bs).foldl (fun r p => g r (f p.1 p.2)) i := by
  cases as
  cases bs
  simp [List.zipWith_foldl_eq_zip_foldl]

@[simp]
theorem zipWith_eq_empty_iff {f : α → β → γ} {as : Array α} {bs : Array β} : zipWith f as bs = #[] ↔ as = #[] ∨ bs = #[] := by
  cases as <;> cases bs <;> simp

theorem map_zipWith {δ : Type _} (f : α → β) (g : γ → δ → α) (cs : Array γ) (ds : Array δ) :
    map f (zipWith g cs ds) = zipWith (fun x y => f (g x y)) cs ds := by
  cases cs
  cases ds
  simp [List.map_zipWith]

theorem take_zipWith : (zipWith f as bs).take n = zipWith f (as.take n) (bs.take n) := by
  cases as
  cases bs
  simp [List.take_zipWith]

theorem extract_zipWith : (zipWith f as bs).extract i j = zipWith f (as.extract i j) (bs.extract i j) := by
  cases as
  cases bs
  simp [List.drop_zipWith, List.take_zipWith]

theorem zipWith_append (f : α → β → γ) (as as' : Array α) (bs bs' : Array β)
    (h : as.size = bs.size) :
    zipWith f (as ++ as') (bs ++ bs') = zipWith f as bs ++ zipWith f as' bs' := by
  cases as
  cases bs
  cases as'
  cases bs'
  simp at h
  simp [List.zipWith_append, h]

theorem zipWith_eq_append_iff {f : α → β → γ} {as : Array α} {bs : Array β} :
    zipWith f as bs = xs ++ ys ↔
      ∃ as₁ as₂ bs₁ bs₂, as₁.size = bs₁.size ∧ as = as₁ ++ as₂ ∧ bs = bs₁ ++ bs₂ ∧ xs = zipWith f as₁ bs₁ ∧ ys = zipWith f as₂ bs₂ := by
  cases as
  cases bs
  cases xs
  cases ys
  simp only [List.zipWith_toArray, List.append_toArray, mk.injEq, List.zipWith_eq_append_iff,
    toArray_eq_append_iff]
  constructor
  · rintro ⟨ws, xs, ys, zs, h, rfl, rfl, rfl, rfl⟩
    exact ⟨ws.toArray, xs.toArray, ys.toArray, zs.toArray, by simp [h]⟩
  · rintro ⟨⟨ws⟩, ⟨xs⟩, ⟨ys⟩, ⟨zs⟩, h, rfl, rfl, h₁, h₂⟩
    exact ⟨ws, xs, ys, zs, by simp_all⟩

@[simp] theorem zipWith_mkArray {a : α} {b : β} {m n : Nat} :
    zipWith f (mkArray m a) (mkArray n b) = mkArray (min m n) (f a b) := by
  simp [← List.toArray_replicate]

theorem map_uncurry_zip_eq_zipWith (f : α → β → γ) (as : Array α) (bs : Array β) :
    map (Function.uncurry f) (as.zip bs) = zipWith f as bs := by
  cases as
  cases bs
  simp [List.map_uncurry_zip_eq_zipWith]

theorem map_zip_eq_zipWith (f : α × β → γ) (as : Array α) (bs : Array β) :
    map f (as.zip bs) = zipWith (Function.curry f) as bs := by
  cases as
  cases bs
  simp [List.map_zip_eq_zipWith]

theorem lt_size_left_of_zipWith {f : α → β → γ} {i : Nat} {as : Array α} {bs : Array β}
    (h : i < (zipWith f as bs).size) : i < as.size := by rw [size_zipWith] at h; omega

theorem lt_size_right_of_zipWith {f : α → β → γ} {i : Nat} {as : Array α} {bs : Array β}
    (h : i < (zipWith f as bs).size) : i < bs.size := by rw [size_zipWith] at h; omega

theorem zipWith_eq_zipWith_take_min (as : Array α) (bs : Array β) :
    zipWith f as bs = zipWith f (as.take (min as.size bs.size)) (bs.take (min as.size bs.size)) := by
  cases as
  cases bs
  simp
  rw [List.zipWith_eq_zipWith_take_min]

theorem reverse_zipWith (h : as.size = bs.size) :
    (zipWith f as bs).reverse = zipWith f as.reverse bs.reverse := by
  cases as
  cases bs
  simp [List.reverse_zipWith (by simpa using h)]

/-! ### zip -/

theorem lt_size_left_of_zip {i : Nat} {as : Array α} {bs : Array β} (h : i < (zip as bs).size) :
    i < as.size :=
  lt_size_left_of_zipWith h

theorem lt_size_right_of_zip {i : Nat} {as : Array α} {bs : Array β} (h : i < (zip as bs).size) :
    i < bs.size :=
  lt_size_right_of_zipWith h

@[simp]
theorem getElem_zip {as : Array α} {bs : Array β} {i : Nat} {h : i < (zip as bs).size} :
    (zip as bs)[i] =
      (as[i]'(lt_size_left_of_zip h), bs[i]'(lt_size_right_of_zip h)) :=
  getElem_zipWith (hi := by simpa using h)

theorem zip_eq_zipWith (as : Array α) (bs : Array β) : zip as bs = zipWith Prod.mk as bs := by
  cases as
  cases bs
  simp [List.zip_eq_zipWith]

theorem zip_map (f : α → γ) (g : β → δ) (as : Array α) (bs : Array β) :
    zip (as.map f) (bs.map g) = (zip as bs).map (Prod.map f g) := by
  cases as
  cases bs
  simp [List.zip_map]

theorem zip_map_left (f : α → γ) (as : Array α) (bs : Array β) :
    zip (as.map f) bs = (zip as bs).map (Prod.map f id) := by rw [← zip_map, map_id]

theorem zip_map_right (f : β → γ) (as : Array α) (bs : Array β) :
    zip as (bs.map f) = (zip as bs).map (Prod.map id f) := by rw [← zip_map, map_id]

theorem zip_append {as bs : Array α} {cs ds : Array β} (_h : as.size = cs.size) :
    zip (as ++ bs) (cs ++ ds) = zip as cs ++ zip bs ds := by
  cases as
  cases cs
  cases bs
  cases ds
  simp_all [List.zip_append]

theorem zip_map' (f : α → β) (g : α → γ) (xs : Array α) :
    zip (xs.map f) (xs.map g) = xs.map fun a => (f a, g a) := by
  cases xs
  simp [List.zip_map']

theorem of_mem_zip {a b} {as : Array α} {bs : Array β} : (a, b) ∈ zip as bs → a ∈ as ∧ b ∈ bs := by
  cases as
  cases bs
  simpa using List.of_mem_zip

theorem map_fst_zip (as : Array α) (bs : Array β) (h : as.size ≤ bs.size) :
    map Prod.fst (zip as bs) = as := by
  cases as
  cases bs
  simp_all [List.map_fst_zip]

theorem map_snd_zip (as : Array α) (bs : Array β) (h : bs.size ≤ as.size) :
    map Prod.snd (zip as bs) = bs := by
  cases as
  cases bs
  simp_all [List.map_snd_zip]

theorem map_prod_left_eq_zip {xs : Array α} (f : α → β) :
    (xs.map fun x => (x, f x)) = xs.zip (xs.map f) := by
  rw [← zip_map']
  congr
  simp

theorem map_prod_right_eq_zip {xs : Array α} (f : α → β) :
    (xs.map fun x => (f x, x)) = (xs.map f).zip xs := by
  rw [← zip_map']
  congr
  simp

@[simp] theorem zip_eq_empty_iff {as : Array α} {bs : Array β} :
    zip as bs = #[] ↔ as = #[] ∨ bs = #[] := by
  cases as
  cases bs
  simp [List.zip_eq_nil_iff]

theorem zip_eq_append_iff {as : Array α} {bs : Array β} :
    zip as bs = xs ++ ys ↔
      ∃ as₁ as₂ bs₁ bs₂, as₁.size = bs₁.size ∧ as = as₁ ++ as₂ ∧ bs = bs₁ ++ bs₂ ∧ xs = zip as₁ bs₁ ∧ ys = zip as₂ bs₂ := by
  simp [zip_eq_zipWith, zipWith_eq_append_iff]

@[simp] theorem zip_mkArray {a : α} {b : β} {m n : Nat} :
    zip (mkArray m a) (mkArray n b) = mkArray (min m n) (a, b) := by
  simp [← List.toArray_replicate]

theorem zip_eq_zip_take_min (as : Array α) (bs : Array β) :
    zip as bs = zip (as.take (min as.size bs.size)) (bs.take (min as.size bs.size)) := by
  cases as
  cases bs
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

theorem zipWithAll_map {μ} (f : Option γ → Option δ → μ) (g : α → γ) (h : β → δ) (as : Array α) (bs : Array β) :
    zipWithAll f (as.map g) (bs.map h) = zipWithAll (fun a b => f (g <$> a) (h <$> b)) as bs := by
  cases as
  cases bs
  simp [List.zipWithAll_map]

theorem zipWithAll_map_left (as : Array α) (bs : Array β) (f : α → α') (g : Option α' → Option β → γ) :
    zipWithAll g (as.map f) bs = zipWithAll (fun a b => g (f <$> a) b) as bs := by
  cases as
  cases bs
  simp [List.zipWithAll_map_left]

theorem zipWithAll_map_right (as : Array α) (bs : Array β) (f : β → β') (g : Option α → Option β' → γ) :
    zipWithAll g as (bs.map f) = zipWithAll (fun a b => g a (f <$> b)) as bs := by
  cases as
  cases bs
  simp [List.zipWithAll_map_right]

theorem map_zipWithAll {δ : Type _} (f : α → β) (g : Option γ → Option δ → α) (cs : Array γ) (ds : Array δ) :
    map f (zipWithAll g cs ds) = zipWithAll (fun x y => f (g x y)) cs ds := by
  cases cs
  cases ds
  simp [List.map_zipWithAll]

@[simp] theorem zipWithAll_replicate {a : α} {b : β} {n : Nat} :
    zipWithAll f (mkArray n a) (mkArray n b) = mkArray n (f a b) := by
  simp [← List.toArray_replicate]

/-! ### unzip -/

@[simp] theorem unzip_fst : (unzip l).fst = l.map Prod.fst := by
  induction l <;> simp_all

@[simp] theorem unzip_snd : (unzip l).snd = l.map Prod.snd := by
  induction l <;> simp_all

theorem unzip_eq_map (xs : Array (α × β)) : unzip xs = (xs.map Prod.fst, xs.map Prod.snd) := by
  cases xs
  simp [List.unzip_eq_map]

theorem zip_unzip (xs : Array (α × β)) : zip (unzip xs).1 (unzip xs).2 = xs := by
  cases xs
  simp only [List.unzip_toArray, Prod.map_fst, Prod.map_snd, List.zip_toArray, List.zip_unzip]

theorem unzip_zip_left {as : Array α} {bs : Array β} (h : as.size ≤ bs.size) :
    (unzip (zip as bs)).1 = as := by
  cases as
  cases bs
  simp_all only [List.size_toArray, List.zip_toArray, List.unzip_toArray, Prod.map_fst,
    List.unzip_zip_left]

theorem unzip_zip_right {as : Array α} {bs : Array β} (h : bs.size ≤ as.size) :
    (unzip (zip as bs)).2 = bs := by
  cases as
  cases bs
  simp_all only [List.size_toArray, List.zip_toArray, List.unzip_toArray, Prod.map_snd,
    List.unzip_zip_right]

theorem unzip_zip {as : Array α} {bs : Array β} (h : as.size = bs.size) :
    unzip (zip as bs) = (as, bs) := by
  cases as
  cases bs
  simp_all only [List.size_toArray, List.zip_toArray, List.unzip_toArray, List.unzip_zip, Prod.map_apply]

theorem zip_of_prod {as : Array α} {bs : Array β} {xs : Array (α × β)} (hl : xs.map Prod.fst = as)
    (hr : xs.map Prod.snd = bs) : xs = as.zip bs := by
  rw [← hl, ← hr, ← zip_unzip xs, ← unzip_fst, ← unzip_snd, zip_unzip, zip_unzip]

@[simp] theorem unzip_mkArray {n : Nat} {a : α} {b : β} :
    unzip (mkArray n (a, b)) = (mkArray n a, mkArray n b) := by
  ext1 <;> simp
