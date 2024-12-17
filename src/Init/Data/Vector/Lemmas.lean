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


/-! ### mk lemmas -/

theorem toArray_mk (a : Array α) (h : a.size = n) : (Vector.mk a h).toArray = a := rfl

@[simp] theorem getElem_mk {data : Array α} {size : data.size = n} {i : Nat} (h : i < n) :
    (Vector.mk data size)[i] = data[i] := rfl

@[simp] theorem getElem?_mk {data : Array α} {size : data.size = n} {i : Nat} :
    (Vector.mk data size)[i]? = data[i]? := by
  subst size
  simp [getElem?_def]

@[simp] theorem mem_mk {data : Array α} {size : data.size = n} {a : α} :
    a ∈ Vector.mk data size ↔ a ∈ data :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp] theorem contains_mk [BEq α] {data : Array α} {size : data.size = n} {a : α} :
    (Vector.mk data size).contains a = data.contains a := by
  simp [contains]

@[simp] theorem push_mk {data : Array α} {size : data.size = n} {x : α} :
    (Vector.mk data size).push x =
      Vector.mk (data.push x) (by simp [size, Nat.succ_eq_add_one]) := rfl

@[simp] theorem pop_mk {data : Array α} {size : data.size = n} :
    (Vector.mk data size).pop = Vector.mk data.pop (by simp [size]) := rfl

@[simp] theorem mk_beq_mk [BEq α] {a b : Array α} {h : a.size = n} {h' : b.size = n} :
    (Vector.mk a h == Vector.mk b h') = (a == b) := by
  simp [instBEq, isEqv, Array.instBEq, Array.isEqv, h, h']

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

@[simp] theorem cast_mk (a : Array α) (h : a.size = n) (h' : n = m) :
    (Vector.mk a h).cast h' = Vector.mk a (by simp [h, h']) := rfl

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

@[simp] theorem anyM_mk [Monad m] (p : α → m Bool) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).anyM p = a.anyM p := rfl

@[simp] theorem allM_mk [Monad m] (p : α → m Bool) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).allM p = a.allM p := rfl

@[simp] theorem any_mk (p : α → Bool) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).any p = a.any p := rfl

@[simp] theorem all_mk (p : α → Bool) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).all p = a.all p := rfl

/-! ### toArray lemmas -/

@[simp] theorem getElem_toArray {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toArray.size) :
    xs.toArray[i] = xs[i]'(by simpa using h) := by
  cases xs
  simp

@[simp] theorem getElem?_toArray {α n} (xs : Vector α n) (i : Nat) :
    xs.toArray[i]? = xs[i]? := by
  cases xs
  simp

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

@[simp] theorem toArray_cast (a : Vector α n) (h : n = m) :
    (a.cast h).toArray = a.toArray := rfl

@[simp] theorem toArray_extract (a : Vector α n) (start stop) :
    (a.extract start stop).toArray = a.toArray.extract start stop := rfl

@[simp] theorem toArray_map (f : α → β) (a : Vector α n) :
    (a.map f).toArray = a.toArray.map f := rfl

@[simp] theorem toArray_ofFn (f : Fin n → α) : (Vector.ofFn f).toArray = Array.ofFn f := rfl

@[simp] theorem toArray_pop (a : Vector α n) : a.pop.toArray = a.toArray.pop := rfl

@[simp] theorem toArray_push (a : Vector α n) (x) : (a.push x).toArray = a.toArray.push x := rfl

@[simp] theorem toArray_beq_toArray [BEq α] (a : Vector α n) (b : Vector α n) :
    (a.toArray == b.toArray) = (a == b) := by
  simp [instBEq, isEqv, Array.instBEq, Array.isEqv, a.2, b.2]

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

@[simp] theorem anyM_toArray [Monad m] (p : α → m Bool) (v : Vector α n) :
    v.toArray.anyM p = v.anyM p := by
  cases v
  simp

@[simp] theorem allM_toArray [Monad m] (p : α → m Bool) (v : Vector α n) :
    v.toArray.allM p = v.allM p := by
  cases v
  simp

@[simp] theorem any_toArray (p : α → Bool) (v : Vector α n) :
    v.toArray.any p = v.any p := by
  cases v
  simp

@[simp] theorem all_toArray (p : α → Bool) (v : Vector α n) :
    v.toArray.all p = v.all p := by
  cases v
  simp

@[simp] theorem toArray_mkVector : (mkVector n a).toArray = mkArray n a := rfl

theorem toArray_inj {v w : Vector α n} : v.toArray = w.toArray ↔ v = w := by
  cases v
  cases w
  simp

/--
`Vector.ext` is an extensionality theorem.
Vectors `a` and `b` are equal to each other if their elements are equal for each valid index.
-/
@[ext]
protected theorem ext {a b : Vector α n} (h : (i : Nat) → (_ : i < n) → a[i] = b[i]) : a = b := by
  apply Vector.toArray_inj.1
  apply Array.ext
  · rw [a.size_toArray, b.size_toArray]
  · intro i hi _
    rw [a.size_toArray] at hi
    exact h i hi

@[simp] theorem toArray_eq_empty_iff (v : Vector α n) : v.toArray = #[] ↔ n = 0 := by
  rcases v with ⟨v, h⟩
  exact ⟨by rintro rfl; simp_all, by rintro rfl; simpa using h⟩

@[simp] theorem mem_toArray_iff (a : α) (v : Vector α n) : a ∈ v.toArray ↔ a ∈ v :=
  ⟨fun h => ⟨h⟩, fun ⟨h⟩ => h⟩

/-! ### toList -/

@[simp] theorem getElem_toList {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toList.length) :
    xs.toList[i] = xs[i]'(by simpa using h) := by
  cases xs
  simp

@[simp] theorem getElem?_toList {α n} (xs : Vector α n) (i : Nat) :
    xs.toList[i]? = xs[i]? := by
  cases xs
  simp

theorem toList_append (a : Vector α m) (b : Vector α n) :
    (a ++ b).toList = a.toList ++ b.toList := by simp

@[simp] theorem toList_drop (a : Vector α n) (m) :
    (a.drop m).toList = a.toList.drop m := by
  simp [List.take_of_length_le]

theorem toList_empty : (#v[] : Vector α 0).toArray = #[] := by simp

theorem toList_mkEmpty (cap) :
    (Vector.mkEmpty (α := α) cap).toList = [] := rfl

theorem toList_eraseIdx (a : Vector α n) (i) (h) :
    (a.eraseIdx i h).toList = a.toList.eraseIdx i := by simp

@[simp] theorem toList_eraseIdx! (a : Vector α n) (i) (hi : i < n) :
    (a.eraseIdx! i).toList = a.toList.eraseIdx i := by
  cases a; simp_all [Array.eraseIdx!]

theorem toList_cast (a : Vector α n) (h : n = m) :
    (a.cast h).toList = a.toList := rfl

theorem toList_extract (a : Vector α n) (start stop) :
    (a.extract start stop).toList = (a.toList.drop start).take (stop - start) := by
  simp

theorem toList_map (f : α → β) (a : Vector α n) :
    (a.map f).toList = a.toList.map f := by simp

theorem toList_ofFn (f : Fin n → α) : (Vector.ofFn f).toList = List.ofFn f := by simp

theorem toList_pop (a : Vector α n) : a.pop.toList = a.toList.dropLast := rfl

theorem toList_push (a : Vector α n) (x) : (a.push x).toList = a.toList ++ [x] := by simp

@[simp] theorem toList_beq_toList [BEq α] (a : Vector α n) (b : Vector α n) :
    (a.toList == b.toList) = (a == b) := by
  simp [instBEq, isEqv, Array.instBEq, Array.isEqv, a.2, b.2]

theorem toList_range : (Vector.range n).toList = List.range n := by simp

theorem toList_reverse (a : Vector α n) : a.reverse.toList = a.toList.reverse := by simp

theorem toList_set (a : Vector α n) (i x h) :
    (a.set i x).toList = a.toList.set i x := rfl

@[simp] theorem toList_setIfInBounds (a : Vector α n) (i x) :
    (a.setIfInBounds i x).toList = a.toList.set i x := by
  simp [Vector.setIfInBounds]

theorem toList_singleton (x : α) : (Vector.singleton x).toList = [x] := rfl

theorem toList_swap (a : Vector α n) (i j) (hi hj) :
    (a.swap i j).toList = (a.toList.set i a[j]).set j a[i] := rfl

@[simp] theorem toList_take (a : Vector α n) (m) : (a.take m).toList = a.toList.take m := by
  simp [List.take_of_length_le]

@[simp] theorem toList_zipWith (f : α → β → γ) (a : Vector α n) (b : Vector β n) :
    (Vector.zipWith a b f).toArray = Array.zipWith a.toArray b.toArray f := rfl

@[simp] theorem anyM_toList [Monad m] (p : α → m Bool) (v : Vector α n) :
    v.toList.anyM p = v.anyM p := by
  cases v
  simp

@[simp] theorem allM_toList [Monad m] [LawfulMonad m] (p : α → m Bool) (v : Vector α n) :
    v.toList.allM p = v.allM p := by
  cases v
  simp

@[simp] theorem any_toList (p : α → Bool) (v : Vector α n) :
    v.toList.any p = v.any p := by
  cases v
  simp

@[simp] theorem all_toList (p : α → Bool) (v : Vector α n) :
    v.toList.all p = v.all p := by
  cases v
  simp

@[simp] theorem toList_mkVector : (mkVector n a).toList = List.replicate n a := rfl

theorem toList_inj {v w : Vector α n} : v.toList = w.toList ↔ v = w := by
  cases v
  cases w
  simp [Array.toList_inj]

@[simp] theorem toList_eq_empty_iff (v : Vector α n) : v.toList = [] ↔ n = 0 := by
  rcases v with ⟨v, h⟩
  simp only [Array.toList_eq_nil_iff]
  exact ⟨by rintro rfl; simp_all, by rintro rfl; simpa using h⟩

@[simp] theorem mem_toList_iff (a : α) (v : Vector α n) : a ∈ v.toList ↔ a ∈ v := by
  simp

theorem length_toList {α n} (xs : Vector α n) : xs.toList.length = n := by simp

/-! ### empty -/

@[simp] theorem empty_eq {xs : Vector α 0} : #v[] = xs ↔ xs = #v[] := by
  cases xs
  simp

/-- A vector of length `0` is the empty vector. -/
protected theorem eq_empty (v : Vector α 0) : v = #v[] := by
  apply Vector.toArray_inj.1
  apply Array.eq_empty_of_size_eq_zero v.2


/-! ### size -/

theorem eq_empty_of_size_eq_zero (xs : Vector α n) (h : n = 0) : xs = #v[].cast h.symm := by
  rcases xs with ⟨xs, rfl⟩
  apply toArray_inj.1
  simp only [List.length_eq_zero, Array.toList_eq_nil_iff] at h
  simp [h]

theorem size_eq_one {xs : Vector α 1} : ∃ a, xs = #v[a] := by
  rcases xs with ⟨xs, h⟩
  simpa using Array.size_eq_one.mp h

/-! ### push -/

theorem back_eq_of_push_eq {a b : α} {xs ys : Vector α n} (h : xs.push a = ys.push b) : a = b := by
  cases xs
  cases ys
  replace h := congrArg Vector.toArray h
  simp only [push_mk] at h
  apply Array.back_eq_of_push_eq h

theorem pop_eq_of_push_eq {a b : α} {xs ys : Vector α n} (h : xs.push a = ys.push b) : xs = ys := by
  cases xs
  cases ys
  replace h := congrArg Vector.toArray h
  simp only [push_mk] at h
  simpa using Array.pop_eq_of_push_eq h

theorem push_inj_left {a : α} {xs ys : Vector α n} : xs.push a = ys.push a ↔ xs = ys :=
  ⟨pop_eq_of_push_eq, fun h => by simp [h]⟩

theorem push_inj_right {a b : α} {xs : Vector α n} : xs.push a = xs.push b ↔ a = b :=
  ⟨back_eq_of_push_eq, fun h => by simp [h]⟩

theorem push_eq_push {a b : α} {xs ys : Vector α n} : xs.push a = ys.push b ↔ a = b ∧ xs = ys := by
  constructor
  · intro h
    exact ⟨back_eq_of_push_eq h, pop_eq_of_push_eq h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem exists_push {xs : Vector α (n + 1)} :
    ∃ (ys : Vector α n) (a : α), xs = ys.push a := by
  rcases xs with ⟨xs, w⟩
  obtain ⟨ys, a, h⟩ := Array.exists_push_of_size_eq_add_one w
  exact ⟨⟨ys, by simp_all⟩, a, toArray_inj.1 h⟩

theorem singleton_inj : #v[a] = #v[b] ↔ a = b := by
  simp

/-! ### mkVector -/

@[simp] theorem mkVector_zero : mkVector 0 a = #v[] := rfl

theorem mkVector_succ : mkVector (n + 1) a = (mkVector n a).push a := by
  simp [mkVector, Array.mkArray_succ]

theorem mkVector_inj : mkVector n a = mkVector n b ↔ n = 0 ∨ a = b := by
  simp [← toArray_inj, toArray_mkVector, Array.mkArray_inj]

/-! ## L[i] and L[i]? -/

@[simp] theorem getElem?_eq_none_iff {a : Vector α n} : a[i]? = none ↔ n ≤ i := by
  by_cases h : i < n
  · simp [getElem?_pos, h]
  · rw [getElem?_neg a i h]
    simp_all

@[simp] theorem none_eq_getElem?_iff {a : Vector α n} {i : Nat} : none = a[i]? ↔ n ≤ i := by
  simp [eq_comm (a := none)]

theorem getElem?_eq_none {a : Vector α n} (h : n ≤ i) : a[i]? = none := by
  simp [getElem?_eq_none_iff, h]

@[simp] theorem getElem?_eq_getElem {a : Vector α n} {i : Nat} (h : i < n) : a[i]? = some a[i] :=
  getElem?_pos ..

theorem getElem?_eq_some_iff {a : Vector α n} : a[i]? = some b ↔ ∃ h : i < n, a[i] = b := by
  simp [getElem?_def]

theorem some_eq_getElem?_iff {a : Vector α n} : some b = a[i]? ↔ ∃ h : i < n, a[i] = b := by
  rw [eq_comm, getElem?_eq_some_iff]

@[simp] theorem some_getElem_eq_getElem?_iff (a : Vector α n) (i : Nat) (h : i < n) :
    (some a[i] = a[i]?) ↔ True := by
  simp [h]

@[simp] theorem getElem?_eq_some_getElem_iff (a : Vector α n) (i : Nat) (h : i < n) :
    (a[i]? = some a[i]) ↔ True := by
  simp [h]

theorem getElem_eq_iff {a : Vector α n} {i : Nat} {h : i < n} : a[i] = x ↔ a[i]? = some x := by
  simp only [getElem?_eq_some_iff]
  exact ⟨fun w => ⟨h, w⟩, fun h => h.2⟩

theorem getElem_eq_getElem?_get (a : Vector α n) (i : Nat) (h : i < n) :
    a[i] = a[i]?.get (by simp [getElem?_eq_getElem, h]) := by
  simp [getElem_eq_iff]

theorem getD_getElem? (a : Vector α n) (i : Nat) (d : α) :
    a[i]?.getD d = if p : i < n then a[i]'p else d := by
  if h : i < n then
    simp [h, getElem?_def]
  else
    have p : i ≥ n := Nat.le_of_not_gt h
    simp [getElem?_eq_none p, h]

@[simp] theorem getElem?_empty {n : Nat} : (#v[] : Vector α 0)[n]? = none := rfl

@[simp] theorem getElem_push_lt {v : Vector α n} {x : α} {i : Nat} (h : i < n) :
    (v.push x)[i] = v[i] := by
  rcases v with ⟨data, rfl⟩
  simp [Array.getElem_push_lt, h]

@[simp] theorem getElem_push_eq (a : Vector α n) (x : α) : (a.push x)[n] = x := by
  rcases a with ⟨a, rfl⟩
  simp

theorem getElem_push (a : Vector α n) (x : α) (i : Nat) (h : i < n + 1) :
    (a.push x)[i] = if h : i < n then a[i] else x := by
  rcases a with ⟨a, rfl⟩
  simp [Array.getElem_push]

theorem getElem?_push {a : Vector α n} {x} : (a.push x)[i]? = if i = n then some x else a[i]? := by
  simp [getElem?_def, getElem_push]
  (repeat' split) <;> first | rfl | omega

@[simp] theorem getElem?_push_size {a : Vector α n} {x} : (a.push x)[n]? = some x := by
  simp [getElem?_push]

@[simp] theorem getElem_singleton (a : α) (h : i < 1) : #v[a][i] = a :=
  match i, h with
  | 0, _ => rfl

theorem getElem?_singleton (a : α) (i : Nat) : #v[a][i]? = if i = 0 then some a else none := by
  simp [List.getElem?_singleton]

/-! ### mem -/

@[simp] theorem getElem_mem {l : Vector α n} {i : Nat} (h : i < n) : l[i] ∈ l := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem not_mem_empty (a : α) : ¬ a ∈ #v[] := nofun

@[simp] theorem mem_push {a : Vector α n} {x y : α} : x ∈ a.push y ↔ x ∈ a ∨ x = y := by
  cases a
  simp

theorem mem_push_self {a : Vector α n} {x : α} : x ∈ a.push x :=
  mem_push.2 (Or.inr rfl)

theorem eq_push_append_of_mem {xs : Vector α n} {x : α} (h : x ∈ xs) :
    ∃ (n₁ n₂ : Nat) (as : Vector α n₁) (bs : Vector α n₂) (h : n₁ + 1 + n₂ = n),
      xs = (as.push x ++ bs).cast h ∧ x ∉ as:= by
  rcases xs with ⟨xs, rfl⟩
  obtain ⟨as, bs, h, w⟩ := Array.eq_push_append_of_mem (by simpa using h)
  simp only at h
  obtain rfl := h
  exact ⟨_, _, as.toVector, bs.toVector, by simp, by simp, by simpa using w⟩

theorem mem_push_of_mem {a : Vector α n} {x : α} (y : α) (h : x ∈ a) : x ∈ a.push y :=
  mem_push.2 (Or.inl h)

theorem exists_mem_of_size_pos (l : Vector α n) (h : 0 < n) : ∃ x, x ∈ l := by
  simpa using List.exists_mem_of_ne_nil l.toList (by simpa using (Nat.ne_of_gt h))

theorem size_zero_iff_forall_not_mem {l : Vector α n} : n = 0 ↔ ∀ a, a ∉ l := by
  simpa using List.eq_nil_iff_forall_not_mem (l := l.toList)

@[simp] theorem mem_dite_empty_left {x : α} [Decidable p] {l : ¬ p → Vector α 0} :
    (x ∈ if h : p then #v[] else l h) ↔ ∃ h : ¬ p, x ∈ l h := by
  split <;> simp_all

@[simp] theorem mem_dite_empty_right {x : α} [Decidable p] {l : p → Vector α 0} :
    (x ∈ if h : p then l h else #v[]) ↔ ∃ h : p, x ∈ l h := by
  split <;> simp_all

@[simp] theorem mem_ite_empty_left {x : α} [Decidable p] {l : Vector α 0} :
    (x ∈ if p then #v[] else l) ↔ ¬ p ∧ x ∈ l := by
  split <;> simp_all

@[simp] theorem mem_ite_empty_right {x : α} [Decidable p] {l : Vector α 0} :
    (x ∈ if p then l else #v[]) ↔ p ∧ x ∈ l := by
  split <;> simp_all

theorem eq_of_mem_singleton (h : a ∈ #v[b]) : a = b := by
  simpa using h

@[simp] theorem mem_singleton {a b : α} : a ∈ #v[b] ↔ a = b :=
  ⟨eq_of_mem_singleton, (by simp [·])⟩

theorem forall_mem_push {p : α → Prop} {xs : Vector α n} {a : α} :
    (∀ x, x ∈ xs.push a → p x) ↔ p a ∧ ∀ x, x ∈ xs → p x := by
  cases xs
  simp [or_comm, forall_eq_or_imp]

theorem forall_mem_ne {a : α} {l : Vector α n} : (∀ a' : α, a' ∈ l → ¬a = a') ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩

theorem forall_mem_ne' {a : α} {l : Vector α n} : (∀ a' : α, a' ∈ l → ¬a' = a) ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩

theorem exists_mem_empty (p : α → Prop) : ¬ (∃ x, ∃ _ : x ∈ #v[], p x) := nofun

theorem forall_mem_empty (p : α → Prop) : ∀ (x) (_ : x ∈ #v[]), p x := nofun

theorem exists_mem_push {p : α → Prop} {a : α} {xs : Vector α n} :
    (∃ x, ∃ _ : x ∈ xs.push a, p x) ↔ p a ∨ ∃ x, ∃ _ : x ∈ xs, p x := by
  simp only [mem_push, exists_prop]
  constructor
  · rintro ⟨x, (h | rfl), h'⟩
    · exact .inr ⟨x, h, h'⟩
    · exact .inl h'
  · rintro (h | ⟨x, h, h'⟩)
    · exact ⟨a, by simp, h⟩
    · exact ⟨x, .inl h, h'⟩

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ (x) (_ : x ∈ #v[a]), p x) ↔ p a := by
  simp only [mem_singleton, forall_eq]

theorem mem_empty_iff (a : α) : a ∈ (#v[] : Vector α 0) ↔ False := by simp

theorem mem_singleton_self (a : α) : a ∈ #v[a] := by simp

theorem mem_of_mem_push_of_mem {a b : α} {l : Vector α n} : a ∈ l.push b → b ∈ l → a ∈ l := by
  rcases l with ⟨l, rfl⟩
  simpa using Array.mem_of_mem_push_of_mem

theorem eq_or_ne_mem_of_mem {a b : α} {l : Vector α n} (h' : a ∈ l.push b) :
    a = b ∨ (a ≠ b ∧ a ∈ l) := by
  if h : a = b then
    exact .inl h
  else
    simp only [mem_push, h, or_false] at h'
    exact .inr ⟨h, h'⟩

theorem size_ne_zero_of_mem {a : α} {l : Vector α n} (h : a ∈ l) : n ≠ 0 := by
  rcases l with ⟨l, rfl⟩
  simpa using Array.ne_empty_of_mem (by simpa using h)

theorem mem_of_ne_of_mem {a y : α} {l : Vector α n} (h₁ : a ≠ y) (h₂ : a ∈ l.push y) : a ∈ l := by
  simpa [h₁] using h₂

theorem ne_of_not_mem_push {a b : α} {l : Vector α n} (h : a ∉ l.push b) : a ≠ b := by
  simp only [mem_push, not_or] at h
  exact h.2

theorem not_mem_of_not_mem_push {a b : α} {l : Vector α n} (h : a ∉ l.push b) : a ∉ l := by
  simp only [mem_push, not_or] at h
  exact h.1

theorem not_mem_push_of_ne_of_not_mem {a y : α} {l : Vector α n} : a ≠ y → a ∉ l → a ∉ l.push y :=
  mt ∘ mem_of_ne_of_mem

theorem ne_and_not_mem_of_not_mem_push {a y : α} {l : Vector α n} : a ∉ l.push y → a ≠ y ∧ a ∉ l := by
  simp +contextual

theorem getElem_of_mem {a} {l : Vector α n} (h : a ∈ l) : ∃ (i : Nat) (h : i < n), l[i]'h = a := by
  rcases l with ⟨l, rfl⟩
  simpa using Array.getElem_of_mem (by simpa using h)

theorem getElem?_of_mem {a} {l : Vector α n} (h : a ∈ l) : ∃ i : Nat, l[i]? = some a :=
  let ⟨n, _, e⟩ := getElem_of_mem h; ⟨n, e ▸ getElem?_eq_getElem _⟩

theorem mem_of_getElem? {l : Vector α n} {i : Nat} {a : α} (e : l[i]? = some a) : a ∈ l :=
  let ⟨_, e⟩ := getElem?_eq_some_iff.1 e; e ▸ getElem_mem ..

theorem mem_iff_getElem {a} {l : Vector α n} : a ∈ l ↔ ∃ (i : Nat) (h : i < n), l[i]'h = a :=
  ⟨getElem_of_mem, fun ⟨_, _, e⟩ => e ▸ getElem_mem ..⟩

theorem mem_iff_getElem? {a} {l : Vector α n} : a ∈ l ↔ ∃ i : Nat, l[i]? = some a := by
  simp [getElem?_eq_some_iff, mem_iff_getElem]

theorem forall_getElem {l : Vector α n} {p : α → Prop} :
    (∀ (i : Nat) h, p (l[i]'h)) ↔ ∀ a, a ∈ l → p a := by
  rcases l with ⟨l, rfl⟩
  simp [Array.forall_getElem]

/-! ### Decidability of bounded quantifiers -/

instance {xs : Vector α n} {p : α → Prop} [DecidablePred p] :
    Decidable (∀ x, x ∈ xs → p x) :=
  decidable_of_iff (∀ (i : Nat) h, p (xs[i]'h)) (by
    simp only [mem_iff_getElem, forall_exists_index]
    exact
      ⟨by rintro w _ i h rfl; exact w i h, fun w i h => w _ i h rfl⟩)

instance {xs : Vector α n} {p : α → Prop} [DecidablePred p] :
    Decidable (∃ x, x ∈ xs ∧ p x) :=
  decidable_of_iff (∃ (i : Nat), ∃ (h : i < n), p (xs[i]'h)) (by
    simp [mem_iff_getElem]
    exact
      ⟨by rintro ⟨i, h, w⟩; exact ⟨_, ⟨i, h, rfl⟩, w⟩, fun ⟨_, ⟨i, h, rfl⟩, w⟩ => ⟨i, h, w⟩⟩)

/-! ### any / all -/

theorem any_iff_exists {p : α → Bool} {xs : Vector α n} :
    xs.any p ↔ ∃ (i : Nat) (_ : i < n), p xs[i] := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.any_iff_exists]

theorem all_iff_forall {p : α → Bool} {xs : Vector α n} :
    xs.all p ↔ ∀ (i : Nat) (_ : i < n), p xs[i] := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.all_iff_forall]

theorem any_eq_true {p : α → Bool} {xs : Vector α n} :
    xs.any p = true ↔ ∃ (i : Nat) (_ : i < n), p xs[i] := by
  simp [any_iff_exists]

theorem any_eq_false {p : α → Bool} {xs : Vector α n} :
    xs.any p = false ↔ ∀ (i : Nat) (_ : i < n), ¬p xs[i] := by
  rw [Bool.eq_false_iff, Ne, any_eq_true]
  simp

theorem allM_eq_not_anyM_not [Monad m] [LawfulMonad m] {p : α → m Bool} {xs : Vector α n} :
    xs.allM p = (! ·) <$> xs.anyM ((! ·) <$> p ·) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.allM_eq_not_anyM_not]

theorem all_eq_not_any_not {p : α → Bool} {xs : Vector α n} :
    xs.all p = !(xs.any (!p ·)) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.all_eq_not_any_not]

@[simp] theorem all_eq_true {p : α → Bool} {xs : Vector α n} :
    xs.all p = true ↔ ∀ (i : Nat) (_ : i < n), p xs[i] := by
  simp [all_iff_forall]

@[simp] theorem all_eq_false {p : α → Bool} {xs : Vector α n} :
    xs.all p = false ↔ ∃ (i : Nat) (_ : i < n), ¬p xs[i] := by
  rw [Bool.eq_false_iff, Ne, all_eq_true]
  simp

theorem all_eq_true_iff_forall_mem {xs : Vector α n} : xs.all p ↔ ∀ x, x ∈ xs → p x := by
  rcases xs with ⟨xs, rfl⟩
  simp only [all_mk, Array.all_eq_true_iff_forall_mem]
  simp

/-- Variant of `any_eq_true` in terms of membership rather than an array index. -/
theorem any_eq_true' {p : α → Bool} {xs : Vector α n} :
    xs.any p = true ↔ (∃ x, x ∈ xs ∧ p x) := by
  rcases xs with ⟨xs, rfl⟩
  simp only [any_mk, Array.any_eq_true']
  simp

/-- Variant of `any_eq_false` in terms of membership rather than an array index. -/
theorem any_eq_false' {p : α → Bool} {xs : Vector α n} :
    xs.any p = false ↔ ∀ x, x ∈ xs → ¬p x := by
  rcases xs with ⟨xs, rfl⟩
  simp only [any_mk, Array.any_eq_false']
  simp

/-- Variant of `all_eq_true` in terms of membership rather than an array index. -/
theorem all_eq_true' {p : α → Bool} {xs : Vector α n} :
    xs.all p = true ↔ ∀ x, x ∈ xs → p x := by
  rcases xs with ⟨xs, rfl⟩
  simp only [all_mk, Array.all_eq_true']
  simp

/-- Variant of `all_eq_false` in terms of membership rather than an array index. -/
theorem all_eq_false' {p : α → Bool} {xs : Vector α n} :
    xs.all p = false ↔ ∃ x, x ∈ xs ∧ ¬p x := by
  rcases xs with ⟨xs, rfl⟩
  simp only [all_mk, Array.all_eq_false']
  simp

theorem any_eq {xs : Vector α n} {p : α → Bool} : xs.any p = decide (∃ i : Nat, ∃ h, p (xs[i]'h)) := by
  by_cases h : xs.any p
  · simp_all [any_eq_true]
  · simp_all [any_eq_false]

/-- Variant of `any_eq` in terms of membership rather than an array index. -/
theorem any_eq' {xs : Vector α n} {p : α → Bool} : xs.any p = decide (∃ x, x ∈ xs ∧ p x) := by
  by_cases h : xs.any p
  · simp_all [any_eq_true']
  · simp only [Bool.not_eq_true] at h
    simp only [h]
    simp only [any_eq_false'] at h
    simpa using h

theorem all_eq {xs : Vector α n} {p : α → Bool} : xs.all p = decide (∀ i, (_ : i < n) → p xs[i]) := by
  by_cases h : xs.all p
  · simp_all [all_eq_true]
  · simp only [Bool.not_eq_true] at h
    simp only [h]
    simp only [all_eq_false] at h
    simpa using h

/-- Variant of `all_eq` in terms of membership rather than an array index. -/
theorem all_eq' {xs : Vector α n} {p : α → Bool} : xs.all p = decide (∀ x, x ∈ xs → p x) := by
  rcases xs with ⟨xs, rfl⟩
  simp only [all_mk, Array.all_eq']
  simp

theorem decide_exists_mem {xs : Vector α n} {p : α → Prop} [DecidablePred p] :
    decide (∃ x, x ∈ xs ∧ p x) = xs.any p := by
  simp [any_eq']

theorem decide_forall_mem {xs : Vector α n} {p : α → Prop} [DecidablePred p] :
    decide (∀ x, x ∈ xs → p x) = xs.all p := by
  simp [all_eq']

theorem any_beq [BEq α] {xs : Vector α n} {a : α} : (xs.any fun x => a == x) = xs.contains a := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.any_beq]

/-- Variant of `any_beq` with `==` reversed. -/
theorem any_beq' [BEq α] [PartialEquivBEq α] {xs : Vector α n} :
    (xs.any fun x => x == a) = xs.contains a := by
  simp only [BEq.comm, any_beq]

theorem all_bne [BEq α] {xs : Vector α n} : (xs.all fun x => a != x) = !xs.contains a := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.all_bne]

/-- Variant of `all_bne` with `!=` reversed. -/
theorem all_bne' [BEq α] [PartialEquivBEq α] {xs : Vector α n} :
    (xs.all fun x => x != a) = !xs.contains a := by
  simp only [bne_comm, all_bne]

theorem mem_of_contains_eq_true [BEq α] [LawfulBEq α] {a : α} {as : Vector α n} :
    as.contains a = true → a ∈ as := by
  rcases as with ⟨as, rfl⟩
  simp [Array.mem_of_contains_eq_true]

theorem contains_eq_true_of_mem [BEq α] [LawfulBEq α] {a : α} {as : Vector α n} (h : a ∈ as) :
    as.contains a = true := by
  rcases as with ⟨as, rfl⟩
  simp only [mem_mk] at h
  simp [Array.contains_eq_true_of_mem, h]

instance [BEq α] [LawfulBEq α] (a : α) (as : Vector α n) : Decidable (a ∈ as) :=
  decidable_of_decidable_of_iff (Iff.intro mem_of_contains_eq_true contains_eq_true_of_mem)

theorem contains_iff [BEq α] [LawfulBEq α] {a : α} {as : Vector α n} :
    as.contains a = true ↔ a ∈ as := ⟨mem_of_contains_eq_true, contains_eq_true_of_mem⟩

@[simp] theorem contains_eq_mem [BEq α] [LawfulBEq α] {a : α} {as : Vector α n} :
    as.contains a = decide (a ∈ as) := by
  rw [Bool.eq_iff_iff, contains_iff, decide_eq_true_iff]

@[simp] theorem any_push [BEq α] {as : Vector α n} {a : α} {p : α → Bool} :
    (as.push a).any p = (as.any p || p a) := by
  rcases as with ⟨as, rfl⟩
  simp [Array.any_push]

@[simp] theorem all_push [BEq α] {as : Vector α n} {a : α} {p : α → Bool} :
    (as.push a).all p = (as.all p && p a) := by
  rcases as with ⟨as, rfl⟩
  simp [Array.all_push]

@[simp] theorem contains_push [BEq α] {l : Vector α n} {a : α} {b : α} :
    (l.push a).contains b = (l.contains b || b == a) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.contains_push]

/-! ### set -/

theorem getElem_set (v : Vector α n) (i : Nat) (x : α) (hi : i < n) (j : Nat) (hj : j < n) :
    (v.set i x hi)[j] = if i = j then x else v[j] := by
  cases v
  split <;> simp_all [Array.getElem_set]

@[simp] theorem getElem_set_self (v : Vector α n) (i : Nat) (x : α) (hi : i < n) :
    (v.set i x hi)[i] = x := by simp [getElem_set]

@[deprecated getElem_set_self (since := "2024-12-12")]
abbrev getElem_set_eq := @getElem_set_self

@[simp] theorem getElem_set_ne (v : Vector α n) (i : Nat) (x : α) (hi : i < n) (j : Nat)
    (hj : j < n) (h : i ≠ j) : (v.set i x hi)[j] = v[j] := by simp [getElem_set, h]

theorem getElem?_set (v : Vector α n) (i : Nat) (hi : i < n) (x : α) (j : Nat) :
    (v.set i x hi)[j]? = if i = j then some x else v[j]? := by
  cases v
  split <;> simp_all [getElem?_eq_getElem, getElem_set]

@[simp] theorem getElem?_set_self (v : Vector α n) (i : Nat) (hi : i < n) (x : α) :
    (v.set i x hi)[i]? = some x := by simp [getElem?_eq_getElem, hi]

@[simp] theorem getElem?_set_ne (v : Vector α n) (i : Nat) (hi : i < n) (x : α) (j : Nat)
    (h : i ≠ j) : (v.set i x hi)[j]? = v[j]? := by
  simp [getElem?_set, h]

@[simp] theorem set_getElem_self {v : Vector α n} {i : Nat} (hi : i < n) :
    v.set i v[i] hi = v := by
  cases v
  simp

theorem set_comm (a b : α) {i j : Nat} (v : Vector α n) {hi : i < n} {hj : j < n} (h : i ≠ j) :
    (v.set i a hi).set j b hj = (v.set j b hj).set i a hi := by
  cases v
  simp [Array.set_comm, h]

@[simp] theorem set_set (a b : α) (v : Vector α n) (i : Nat) (hi : i < n) :
    (v.set i a hi).set i b hi = v.set i b hi := by
  cases v
  simp

theorem mem_set (v : Vector α n) (i : Nat) (hi : i < n) (a : α) :
    a ∈ v.set i a hi := by
  simp [mem_iff_getElem]
  exact ⟨i, (by simpa using hi), by simp⟩

theorem mem_or_eq_of_mem_set {v : Vector α n} {i : Nat} {a b : α} {w : i < n} (h : a ∈ v.set i b) : a ∈ v ∨ a = b := by
  cases v
  simpa using Array.mem_or_eq_of_mem_set (by simpa using h)

/-! ### setIfInBounds -/

theorem getElem_setIfInBounds (a : Vector α n) (i : Nat) (x : α) (j : Nat)
    (hj : j < n) : (a.setIfInBounds i x)[j] = if i = j then x else a[j] := by
  cases a
  split <;> simp_all [Array.getElem_setIfInBounds]

@[simp] theorem getElem_setIfInBounds_self (v : Vector α n) (i : Nat) (x : α) (hi : i < n) :
    (v.setIfInBounds i x)[i] = x := by simp [getElem_setIfInBounds, hi]

@[deprecated getElem_setIfInBounds_self (since := "2024-12-12")]
abbrev getElem_setIfInBounds_eq := @getElem_setIfInBounds_self

@[simp] theorem getElem_setIfInBounds_ne (v : Vector α n) (i : Nat) (x : α) (j : Nat)
    (hj : j < n) (h : i ≠ j) : (v.setIfInBounds i x)[j] = v[j] := by simp [getElem_setIfInBounds, h]

theorem getElem?_setIfInBounds (v : Vector α n) (i : Nat) (x : α) (j : Nat) :
    (v.setIfInBounds i x)[j]? = if i = j then if i < n then some x else none else v[j]? := by
  rcases v with ⟨v, rfl⟩
  simp [Array.getElem?_setIfInBounds]

theorem getElem?_setIfInBounds_self (v : Vector α n) (i : Nat) (x : α) :
    (v.setIfInBounds i x)[i]? = if i < n then some x else none := by simp [getElem?_setIfInBounds]

@[simp] theorem getElem?_setIfInBounds_self_of_lt (v : Vector α n) (i : Nat) (x : α) (h : i < n) :
    (v.setIfInBounds i x)[i]? = some x := by simp [getElem?_setIfInBounds, h]

@[simp] theorem getElem?_setIfInBounds_ne (a : Vector α n) (i : Nat) (x : α) (j : Nat)
    (h : i ≠ j) : (a.setIfInBounds i x)[j]? = a[j]? := by simp [getElem?_setIfInBounds, h]

theorem setIfInBounds_eq_of_size_le {l : Vector α n} {m : Nat} (h : l.size ≤ m) {a : α} :
    l.setIfInBounds m a = l := by
  rcases l with ⟨l, rfl⟩
  simp [Array.setIfInBounds_eq_of_size_le (by simpa using h)]

theorem setIfInBound_comm (a b : α) {i j : Nat} (v : Vector α n) (h : i ≠ j) :
    (v.setIfInBounds i a).setIfInBounds j b = (v.setIfInBounds j b).setIfInBounds i a := by
  rcases v with ⟨v, rfl⟩
  simp only [setIfInBounds_mk, mk.injEq]
  rw [Array.setIfInBounds_comm _ _ _ h]

@[simp] theorem setIfInBounds_setIfInBounds (a b : α) (v : Vector α n) (i : Nat) :
    (v.setIfInBounds i a).setIfInBounds i b = v.setIfInBounds i b := by
  rcases v with ⟨v, rfl⟩
  simp

theorem mem_setIfInBounds (v : Vector α n) (i : Nat) (hi : i < n) (a : α) :
    a ∈ v.setIfInBounds i a := by
  simp [mem_iff_getElem]
  exact ⟨i, (by simpa using hi), by simp⟩

/-! ### BEq -/

@[simp] theorem push_beq_push [BEq α] {a b : α} {n : Nat} {v : Vector α n} {w : Vector α n} :
    (v.push a == w.push b) = (v == w && a == b) := by
  cases v
  cases w
  simp

@[simp] theorem mkVector_beq_mkVector [BEq α] {a b : α} {n : Nat} :
    (mkVector n a == mkVector n b) = (n == 0 || a == b) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mkVector_succ, mkVector_succ, push_beq_push, mkVector_beq_mkVector]
    rw [Bool.eq_iff_iff]
    simp +contextual

@[simp] theorem reflBEq_iff [BEq α] [NeZero n] : ReflBEq (Vector α n) ↔ ReflBEq α := by
  match n, NeZero.ne n with
  | n + 1, _ =>
    constructor
    · intro h
      constructor
      intro a
      suffices (mkVector (n + 1) a == mkVector (n + 1) a) = true by
        rw [mkVector_succ, push_beq_push, Bool.and_eq_true] at this
        exact this.2
      simp
    · intro h
      constructor
      rintro ⟨v, h⟩
      simpa using Array.isEqv_self_beq ..

@[simp] theorem lawfulBEq_iff [BEq α] [NeZero n] : LawfulBEq (Vector α n) ↔ LawfulBEq α := by
  match n, NeZero.ne n with
  | n + 1, _ =>
    constructor
    · intro h
      constructor
      · intro a b h
        have := mkVector_inj (n := n+1) (a := a) (b := b)
        simp only [Nat.add_one_ne_zero, false_or] at this
        rw [← this]
        apply eq_of_beq
        rw [mkVector_beq_mkVector]
        simpa
      · intro a
        suffices (mkVector (n + 1) a == mkVector (n + 1) a) = true by
          rw [mkVector_beq_mkVector] at this
          simpa
        simp
    · intro h
      constructor
      · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
        simp at h
        obtain ⟨hs, hi⟩ := Array.rel_of_isEqv h
        ext i h
        · simpa using hi _ (by omega)
      · rintro ⟨a, ha⟩
        simpa using Array.isEqv_self_beq ..

/-! Content below this point has not yet been aligned with `List` and `Array`. -/

@[simp] theorem getElem_ofFn {α n} (f : Fin n → α) (i : Nat) (h : i < n) :
    (Vector.ofFn f)[i] = f ⟨i, by simpa using h⟩ := by
  simp [ofFn]

/-- The empty vector maps to the empty vector. -/
@[simp]
theorem map_empty (f : α → β) : map f #v[] = #v[] := by
  rw [map, mk.injEq]
  exact Array.map_empty f

@[simp] theorem getElem_push_last {v : Vector α n} {x : α} : (v.push x)[n] = x := by
  rcases v with ⟨data, rfl⟩
  simp

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

/-! ### append -/

theorem getElem_append (a : Vector α n) (b : Vector α m) (i : Nat) (hi : i < n + m) :
    (a ++ b)[i] = if h : i < n then a[i] else b[i - n] := by
  rcases a with ⟨a, rfl⟩
  rcases b with ⟨b, rfl⟩
  simp [Array.getElem_append, hi]

theorem getElem_append_left {a : Vector α n} {b : Vector α m} {i : Nat} (hi : i < n) :
    (a ++ b)[i] = a[i] := by simp [getElem_append, hi]

theorem getElem_append_right {a : Vector α n} {b : Vector α m} {i : Nat} (h : i < n + m) (hi : n ≤ i) :
    (a ++ b)[i] = b[i - n] := by
  rw [getElem_append, dif_neg (by omega)]

/-! ### cast -/

@[simp] theorem getElem_cast (a : Vector α n) (h : n = m) (i : Nat) (hi : i < m) :
    (a.cast h)[i] = a[i] := by
  cases a
  simp

/-! ### extract -/

@[simp] theorem getElem_extract (a : Vector α n) (start stop) (i : Nat) (hi : i < min stop n - start) :
    (a.extract start stop)[i] = a[start + i] := by
  cases a
  simp

/-! ### map -/

@[simp] theorem getElem_map (f : α → β) (a : Vector α n) (i : Nat) (hi : i < n) :
    (a.map f)[i] = f a[i] := by
  cases a
  simp

/-! ### zipWith -/

@[simp] theorem getElem_zipWith (f : α → β → γ) (a : Vector α n) (b : Vector β n) (i : Nat)
    (hi : i < n) : (zipWith a b f)[i] = f a[i] b[i] := by
  cases a
  cases b
  simp

/-! ### swap -/

theorem getElem_swap (a : Vector α n) (i j : Nat) {hi hj} (k : Nat) (hk : k < n) :
    (a.swap i j hi hj)[k] = if k = i then a[j] else if k = j then a[i] else a[k] := by
  cases a
  simp_all [Array.getElem_swap]

@[simp] theorem getElem_swap_right (a : Vector α n) {i j : Nat} {hi hj} :
    (a.swap i j hi hj)[j]'(by simpa using hj) = a[i] := by
  simp +contextual [getElem_swap]

@[simp] theorem getElem_swap_left (a : Vector α n) {i j : Nat} {hi hj} :
    (a.swap i j hi hj)[i]'(by simpa using hi) = a[j] := by
  simp [getElem_swap]

@[simp] theorem getElem_swap_of_ne (a : Vector α n) {i j : Nat} {hi hj} (hp : p < n)
    (hi' : p ≠ i) (hj' : p ≠ j) : (a.swap i j hi hj)[p] = a[p] := by
  simp_all [getElem_swap]

@[simp] theorem swap_swap (a : Vector α n) {i j : Nat} {hi hj} :
    (a.swap i j hi hj).swap i j hi hj = a := by
  cases a
  simp_all [Array.swap_swap]

theorem swap_comm (a : Vector α n) {i j : Nat} {hi hj} :
    a.swap i j hi hj = a.swap j i hj hi := by
  cases a
  simp only [swap_mk, mk.injEq]
  rw [Array.swap_comm]

/-! ### range -/

@[simp] theorem getElem_range (i : Nat) (hi : i < n) : (Vector.range n)[i] = i := by
  simp [Vector.range]

/-! ### take -/

@[simp] theorem getElem_take (a : Vector α n) (m : Nat) (hi : i < min n m) :
    (a.take m)[i] = a[i] := by
  cases a
  simp

/-! ### drop -/

@[simp] theorem getElem_drop (a : Vector α n) (m : Nat) (hi : i < n - m) :
    (a.drop m)[i] = a[m + i] := by
  cases a
  simp

/-! ### reverse -/

@[simp] theorem getElem_reverse (a : Vector α n) (i : Nat) (hi : i < n) :
    (a.reverse)[i] = a[n - 1 - i] := by
  rcases a with ⟨a, rfl⟩
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
