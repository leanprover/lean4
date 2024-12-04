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

namespace Array

theorem toVector_inj {a b : Array α} (h₁ : a.size = b.size) (h₂ : a.toVector.cast h₁ = b.toVector) : a = b := by
  ext i ih₁ ih₂
  · exact h₁
  · simpa using congrArg (fun a => a[i]) h₂

end Array

namespace Vector

@[simp] theorem getElem_mk {data : Array α} {size : data.size = n} {i : Nat} (h : i < n) :
    (Vector.mk data size)[i] = data[i] := rfl

@[simp] theorem getElem_toArray {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toArray.size) :
    xs.toArray[i] = xs[i]'(by simpa using h) := by
  cases xs
  simp

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


/-! ### mk lemmas -/

theorem toArray_mk (a : Array α) (h : a.size = n) : (Vector.mk a h).toArray = a := rfl

@[simp] theorem allDiff_mk [BEq α] (a : Array α) (h : a.size = n) :
    (Vector.mk a h).allDiff = a.allDiff := rfl

@[simp] theorem mk_append_mk (a b : Array α) (ha : a.size = n) (hb : b.size = m) :
    Vector.mk a ha ++ Vector.mk b hb = Vector.mk (a ++ b) (by simp [ha, hb]) := rfl

@[simp] theorem back!_mk [Inhabited α] (a : Array α) (h : a.size = n) :
    (Vector.mk a h).back! = a.back! := rfl

@[simp] theorem back?_mk (a : Array α) (h : a.size = n) :
    (Vector.mk a h).back? = a.back? := rfl

@[simp] theorem drop_mk (a : Array α) (h : a.size = n) (m) :
    (Vector.mk a h).drop m = Vector.mk (a.extract m a.size) (by simp [h]) := rfl

@[simp] theorem eraseIdx_mk (a : Array α) (h : a.size = n) (i) (h') :
    (Vector.mk a h).eraseIdx i h' = Vector.mk (a.eraseIdx i) (by simp [h]) := rfl

@[simp] theorem eraseIdx!_mk (a : Array α) (h : a.size = n) (i) (hi : i < n) :
    (Vector.mk a h).eraseIdx! i = Vector.mk (a.eraseIdx i) (by simp [h, hi]) := by
  simp [Vector.eraseIdx!, hi]

@[simp] theorem extract_mk (a : Array α) (h : a.size = n) (start stop) :
    (Vector.mk a h).extract start stop = Vector.mk (a.extract start stop) (by simp [h]) := rfl

@[simp] theorem indexOf?_mk [BEq α] (a : Array α) (h : a.size = n) (x : α) :
    (Vector.mk a h).indexOf? x = (a.indexOf? x).map (Fin.cast h) := rfl

@[simp] theorem mk_isEqv_mk (r : α → α → Bool) (a b : Array α) (ha : a.size = n) (hb : b.size = n) :
    Vector.isEqv (Vector.mk a ha) (Vector.mk b hb) r = Array.isEqv a b r := by
  simp [Vector.isEqv, Array.isEqv, ha, hb]

@[simp] theorem mk_isPrefixOf_mk [BEq α] (a b : Array α) (ha : a.size = n) (hb : b.size = m) :
    (Vector.mk a ha).isPrefixOf (Vector.mk b hb) = a.isPrefixOf b := rfl

@[simp] theorem map_mk (a : Array α) (h : a.size = n) (f : α → β) :
    (Vector.mk a h).map f = Vector.mk (a.map f) (by simp [h]) := rfl

@[simp] theorem reverse_mk (a : Array α) (h : a.size = n) :
    (Vector.mk a h).reverse = Vector.mk a.reverse (by simp [h]) := rfl

@[simp] theorem set_mk (a : Array α) (h : a.size = n) (i x w) :
    (Vector.mk a h).set i x = Vector.mk (a.set i x) (by simp [h]) := rfl

@[simp] theorem set!_mk (a : Array α) (h : a.size = n) (i x) :
    (Vector.mk a h).set! i x = Vector.mk (a.set! i x) (by simp [h]) := rfl

@[simp] theorem setIfInBounds_mk (a : Array α) (h : a.size = n) (i x) :
    (Vector.mk a h).setIfInBounds i x = Vector.mk (a.setIfInBounds i x) (by simp [h]) := rfl

@[simp] theorem swap_mk (a : Array α) (h : a.size = n) (i j) (hi hj) :
    (Vector.mk a h).swap i j = Vector.mk (a.swap i j) (by simp [h]) :=
  rfl

@[simp] theorem swapIfInBounds_mk (a : Array α) (h : a.size = n) (i j) :
    (Vector.mk a h).swapIfInBounds i j = Vector.mk (a.swapIfInBounds i j) (by simp [h]) := rfl

@[simp] theorem swapAt_mk (a : Array α) (h : a.size = n) (i x) (hi) :
    (Vector.mk a h).swapAt i x =
      ((a.swapAt i x).fst, Vector.mk (a.swapAt i x).snd (by simp [h])) :=
  rfl

@[simp] theorem swapAt!_mk (a : Array α) (h : a.size = n) (i x) : (Vector.mk a h).swapAt! i x =
    ((a.swapAt! i x).fst, Vector.mk (a.swapAt! i x).snd (by simp [h])) := rfl

@[simp] theorem take_mk (a : Array α) (h : a.size = n) (m) :
    (Vector.mk a h).take m = Vector.mk (a.take m) (by simp [h]) := rfl

@[simp] theorem mk_zipWith_mk (f : α → β → γ) (a : Array α) (b : Array β)
      (ha : a.size = n) (hb : b.size = n) : zipWith (Vector.mk a ha) (Vector.mk b hb) f =
        Vector.mk (Array.zipWith a b f) (by simp [ha, hb]) := rfl

/-! ### toArray lemmas -/

@[simp] theorem toArray_append (a : Vector α m) (b : Vector α n) :
    (a ++ b).toArray = a.toArray ++ b.toArray := rfl

@[simp] theorem toArray_drop (a : Vector α n) (m) :
    (a.drop m).toArray = a.toArray.extract m a.size := rfl

@[simp] theorem toArray_empty : (#v[] : Vector α 0).toArray = #[] := rfl

@[simp] theorem toArray_mkEmpty (cap) :
    (Vector.mkEmpty (α := α) cap).toArray = Array.mkEmpty cap := rfl

@[simp] theorem toArray_eraseIdx (a : Vector α n) (i) (h) :
    (a.eraseIdx i h).toArray = a.toArray.eraseIdx i (by simp [h]) := rfl

@[simp] theorem toArray_eraseIdx! (a : Vector α n) (i) (hi : i < n) :
    (a.eraseIdx! i).toArray = a.toArray.eraseIdx! i := by
  cases a; simp_all [Array.eraseIdx!]

@[simp] theorem toArray_extract (a : Vector α n) (start stop) :
    (a.extract start stop).toArray = a.toArray.extract start stop := rfl

@[simp] theorem toArray_map (f : α → β) (a : Vector α n) :
    (a.map f).toArray = a.toArray.map f := rfl

@[simp] theorem toArray_ofFn (f : Fin n → α) : (Vector.ofFn f).toArray = Array.ofFn f := rfl

@[simp] theorem toArray_pop (a : Vector α n) : a.pop.toArray = a.toArray.pop := rfl

@[simp] theorem toArray_push (a : Vector α n) (x) : (a.push x).toArray = a.toArray.push x := rfl

@[simp] theorem toArray_range : (Vector.range n).toArray = Array.range n := rfl

@[simp] theorem toArray_reverse (a : Vector α n) : a.reverse.toArray = a.toArray.reverse := rfl

@[simp] theorem toArray_set (a : Vector α n) (i x h) :
    (a.set i x).toArray = a.toArray.set i x (by simpa using h):= rfl

@[simp] theorem toArray_set! (a : Vector α n) (i x) :
    (a.set! i x).toArray = a.toArray.set! i x := rfl

@[simp] theorem toArray_setIfInBounds (a : Vector α n) (i x) :
    (a.setIfInBounds i x).toArray = a.toArray.setIfInBounds i x := rfl

@[simp] theorem toArray_singleton (x : α) : (Vector.singleton x).toArray = #[x] := rfl

@[simp] theorem toArray_swap (a : Vector α n) (i j) (hi hj) : (a.swap i j).toArray =
    a.toArray.swap i j (by simp [hi, hj]) (by simp [hi, hj]) := rfl

@[simp] theorem toArray_swapIfInBounds (a : Vector α n) (i j) :
    (a.swapIfInBounds i j).toArray = a.toArray.swapIfInBounds i j := rfl

@[simp] theorem toArray_swapAt (a : Vector α n) (i x h) :
    ((a.swapAt i x).fst, (a.swapAt i x).snd.toArray) =
      ((a.toArray.swapAt i x (by simpa using h)).fst,
        (a.toArray.swapAt i x (by simpa using h)).snd) := rfl

@[simp] theorem toArray_swapAt! (a : Vector α n) (i x) :
    ((a.swapAt! i x).fst, (a.swapAt! i x).snd.toArray) =
      ((a.toArray.swapAt! i x).fst, (a.toArray.swapAt! i x).snd) := rfl

@[simp] theorem toArray_take (a : Vector α n) (m) : (a.take m).toArray = a.toArray.take m := rfl

@[simp] theorem toArray_zipWith (f : α → β → γ) (a : Vector α n) (b : Vector β n) :
    (Vector.zipWith a b f).toArray = Array.zipWith a.toArray b.toArray f := rfl

/-! ### toList lemmas -/

theorem length_toList {α n} (xs : Vector α n) : xs.toList.length = n := by simp

theorem getElem_toList {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toList.length) :
    xs.toList[i] = xs[i]'(by simpa using h) := by simp

theorem toList_inj {a b : Vector α n} (h : a.toList = b.toList) : a = b := by
  rcases a with ⟨⟨a⟩, ha⟩
  rcases b with ⟨⟨b⟩, hb⟩
  simpa using h

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
