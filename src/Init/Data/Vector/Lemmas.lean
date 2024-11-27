/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Francois Dorais
-/
prelude
import Init.Data.Vector.Basic

/-!
## Vectors
Lemmas about `Vector α n`
-/

namespace Vector

theorem length_toList {α n} (xs : Vector α n) : xs.toList.length = n := by simp

@[simp] theorem getElem_mk {data : Array α} {size : data.size = n} {i : Nat} (h : i < n) :
    (Vector.mk data size)[i] = data[i] := rfl

@[simp] theorem getElem_toArray {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toArray.size) :
    xs.toArray[i] = xs[i]'(by simpa using h) := by
  cases xs
  simp

theorem getElem_toList {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toList.length) :
    xs.toList[i] = xs[i]'(by simpa using h) := by simp

@[simp] theorem getElem_ofFn {α n} (f : Fin n → α) (i : Nat) (h : i < n) :
    (Vector.ofFn f)[i] = f ⟨i, by simpa using h⟩ := by
  simp [ofFn]

/-- The empty vector maps to the empty vector. -/
@[simp]
theorem map_empty (f : α → β) : map f #v[] = #v[] := by
  rw [map, mk.injEq]
  exact Array.map_empty f

theorem toArray_inj : ∀ {v w : Vector α n}, v.toArray = w.toArray → v = w
  | {..}, {..}, rfl => rfl

/-- A vector of length `0` is the empty vector. -/
protected theorem eq_empty (v : Vector α 0) : v = #v[] := by
  apply Vector.toArray_inj
  apply Array.eq_empty_of_size_eq_zero v.2

/--
`Vector.ext` is an extensionality theorem.
Vectors `a` and `b` are equal to each other if their elements are equal for each valid index.
-/
@[ext]
protected theorem ext {a b : Vector α n} (h : (i : Nat) → (_ : i < n) → a[i] = b[i]) : a = b := by
  apply Vector.toArray_inj
  apply Array.ext
  · rw [a.size_toArray, b.size_toArray]
  · intro i hi _
    rw [a.size_toArray] at hi
    exact h i hi

@[simp] theorem push_mk {data : Array α} {size : data.size = n} {x : α} :
    (Vector.mk data size).push x =
      Vector.mk (data.push x) (by simp [size, Nat.succ_eq_add_one]) := rfl

@[simp] theorem pop_mk {data : Array α} {size : data.size = n} :
    (Vector.mk data size).pop = Vector.mk data.pop (by simp [size]) := rfl

@[simp] theorem swap_mk {data : Array α} {size : data.size = n} {i j : Nat} {hi hj} :
    (Vector.mk data size).swap i j hi hj = Vector.mk (data.swap i j) (by simp_all) := rfl

@[simp] theorem getElem_push_last {v : Vector α n} {x : α} : (v.push x)[n] = x := by
  rcases v with ⟨data, rfl⟩
  simp

@[simp] theorem getElem_push_lt {v : Vector α n} {x : α} {i : Nat} (h : i < n) :
    (v.push x)[i] = v[i] := by
  rcases v with ⟨data, rfl⟩
  simp [Array.getElem_push_lt, h]

@[simp] theorem getElem_pop {v : Vector α n} {i : Nat} (h : i < n - 1) : (v.pop)[i] = v[i] := by
  rcases v with ⟨data, rfl⟩
  simp

/--
Variant of `getElem_pop` that will sometimes fire when `getElem_pop` gets stuck because of
defeq issues in the implicit size argument.
-/
@[simp] theorem getElem_pop' (v : Vector α (n + 1)) (i : Nat) (h : i < n + 1 - 1) :
    @getElem (Vector α n) Nat α (fun _ i => i < n) instGetElemNatLt v.pop i h = v[i] :=
  getElem_pop h

@[simp] theorem push_pop_back (v : Vector α (n + 1)) : v.pop.push v.back = v := by
  ext i
  by_cases h : i < n
  · simp [h]
  · replace h : i = v.size - 1 := by rw [size_toArray]; omega
    subst h
    simp [pop, back, back!, ← Array.eq_push_pop_back!_of_size_ne_zero]

theorem push_swap (a : Vector α n) (x : α) {i j : Nat} {hi hj} :
    (a.swap i j hi hj).push x = (a.push x).swap i j := by
  cases a
  simp [Array.push_swap]

/-! ### cast -/

@[simp] theorem cast_mk {n m} (a : Array α) (w : a.size = n) (h : n = m) :
    (Vector.mk a w).cast h = ⟨a, h ▸ w⟩ := by
  simp [Vector.cast]

@[simp] theorem cast_refl {n} (a : Vector α n) : a.cast rfl = a := by
  cases a
  simp

@[simp] theorem toArray_cast {n m} (a : Vector α n) (h : n = m) :
    (a.cast h).toArray = a.toArray := by
  subst h
  simp

theorem cast_inj {n m} (a : Vector α n) (b : Vector α n) (h : n = m) :
    a.cast h = b.cast h ↔ a = b := by
  cases h
  simp

theorem cast_eq_iff {n m} (a : Vector α n) (b : Vector α m) (h : n = m) :
    a.cast h = b ↔ a = b.cast h.symm := by
  cases h
  simp

theorem eq_cast_iff {n m} (a : Vector α n) (b : Vector α m) (h : m = n) :
    a = b.cast h ↔ a.cast h.symm = b := by
  cases h
  simp

/-! ### Decidable quantifiers. -/

theorem forall_zero_iff {P : Vector α 0 → Prop} :
    (∀ v, P v) ↔ P #v[] := by
  constructor
  · intro h
    apply h
  · intro h v
    obtain (rfl : v = #v[]) := (by ext i h; simp at h)
    apply h

theorem forall_cons_iff {P : Vector α (n + 1) → Prop} :
    (∀ v : Vector α (n + 1), P v) ↔ (∀ (x : α) (v : Vector α n), P (v.push x)) := by
  constructor
  · intro h _ _
    apply h
  · intro h v
    have w : v = v.pop.push v.back := by simp
    rw [w]
    apply h

instance instDecidableForallVectorZero (P : Vector α 0 → Prop) :
    ∀ [Decidable (P #v[])], Decidable (∀ v, P v)
  | .isTrue h => .isTrue fun ⟨v, s⟩ => by
    obtain (rfl : v = .empty) := (by ext i h₁ h₂; exact s; cases h₂)
    exact h
  | .isFalse h => .isFalse (fun w => h (w _))

instance instDecidableForallVectorSucc (P : Vector α (n+1) → Prop)
    [Decidable (∀ (x : α) (v : Vector α n), P (v.push x))] : Decidable (∀ v, P v) :=
  decidable_of_iff' (∀ x (v : Vector α n), P (v.push x)) forall_cons_iff

instance instDecidableExistsVectorZero (P : Vector α 0 → Prop) [Decidable (P #v[])] :
    Decidable (∃ v, P v) :=
  decidable_of_iff (¬ ∀ v, ¬ P v) Classical.not_forall_not

instance instDecidableExistsVectorSucc (P : Vector α (n+1) → Prop)
    [Decidable (∀ (x : α) (v : Vector α n), ¬ P (v.push x))] : Decidable (∃ v, P v) :=
  decidable_of_iff (¬ ∀ v, ¬ P v) Classical.not_forall_not
