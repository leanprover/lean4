/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Francois Dorais, Kim Morrison
-/
prelude
import Init.Data.Vector.Basic
import Init.Data.Array.Attach

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

@[simp] theorem mk_toArray (v : Vector α n) : mk v.toArray v.2 = v := by
  rfl

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

@[simp] theorem back_mk [NeZero n] (a : Array α) (h : a.size = n) :
    (Vector.mk a h).back =
      a[n - 1]'(Nat.lt_of_lt_of_eq (Nat.sub_one_lt (NeZero.ne n)) h.symm) := rfl

@[simp] theorem foldlM_mk [Monad m] (f : β → α → m β) (b : β) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).foldlM f b = a.foldlM f b := rfl

@[simp] theorem foldrM_mk [Monad m] (f : α → β → m β) (b : β) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).foldrM f b = a.foldrM f b := rfl

@[simp] theorem foldl_mk (f : β → α → β) (b : β) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).foldl f b = a.foldl f b := rfl

@[simp] theorem foldr_mk (f : α → β → β) (b : β) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).foldr f b = a.foldr f b := rfl

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

@[simp] theorem finIdxOf?_mk [BEq α] (a : Array α) (h : a.size = n) (x : α) :
    (Vector.mk a h).finIdxOf? x = (a.finIdxOf? x).map (Fin.cast h) := rfl

@[deprecated finIdxOf?_mk (since := "2025-01-29")]
abbrev indexOf?_mk := @finIdxOf?_mk

@[simp] theorem findM?_mk [Monad m] (a : Array α) (h : a.size = n) (f : α → m Bool) :
    (Vector.mk a h).findM? f = a.findM? f := rfl

@[simp] theorem findSomeM?_mk [Monad m] (a : Array α) (h : a.size = n) (f : α → m (Option β)) :
    (Vector.mk a h).findSomeM? f = a.findSomeM? f := rfl

@[simp] theorem mk_isEqv_mk (r : α → α → Bool) (a b : Array α) (ha : a.size = n) (hb : b.size = n) :
    Vector.isEqv (Vector.mk a ha) (Vector.mk b hb) r = Array.isEqv a b r := by
  simp [Vector.isEqv, Array.isEqv, ha, hb]

@[simp] theorem mk_isPrefixOf_mk [BEq α] (a b : Array α) (ha : a.size = n) (hb : b.size = m) :
    (Vector.mk a ha).isPrefixOf (Vector.mk b hb) = a.isPrefixOf b := rfl

@[simp] theorem map_mk (a : Array α) (h : a.size = n) (f : α → β) :
    (Vector.mk a h).map f = Vector.mk (a.map f) (by simp [h]) := rfl

@[simp] theorem mapIdx_mk (a : Array α) (h : a.size = n) (f : Nat → α → β) :
    (Vector.mk a h).mapIdx f = Vector.mk (a.mapIdx f) (by simp [h]) := rfl

@[simp] theorem mapFinIdx_mk (a : Array α) (h : a.size = n) (f : (i : Nat) → α → (h : i < n) → β) :
    (Vector.mk a h).mapFinIdx f =
      Vector.mk (a.mapFinIdx fun i a h' => f i a (by simpa [h] using h')) (by simp [h]) := rfl

@[simp] theorem forM_mk [Monad m] (f : α → m PUnit) (a : Array α) (h : a.size = n) :
    forM (Vector.mk a h) f = forM a f := rfl

@[simp] theorem forIn'_mk [Monad m]
    (xs : Array α) (h : xs.size = n) (b : β)
    (f : (a : α) → a ∈ Vector.mk xs h → β → m (ForInStep β)) :
    forIn' (Vector.mk xs h) b f = forIn' xs b (fun a m b => f a (by simpa using m) b) := rfl

@[simp] theorem forIn_mk [Monad m]
    (xs : Array α) (h : xs.size = n) (b : β) (f : (a : α) → β → m (ForInStep β)) :
    forIn (Vector.mk xs h) b f = forIn xs b f := rfl

@[simp] theorem flatMap_mk (f : α → Vector β m) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).flatMap f =
      Vector.mk (a.flatMap (fun a => (f a).toArray)) (by simp [h, Array.map_const']) := rfl

@[simp] theorem firstM_mk [Alternative m] (f : α → m β) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).firstM f = a.firstM f := rfl

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

@[simp] theorem zipIdx_mk (a : Array α) (h : a.size = n) (k : Nat := 0) :
    (Vector.mk a h).zipIdx k = Vector.mk (a.zipIdx k) (by simp [h]) := rfl

@[deprecated zipIdx_mk (since := "2025-01-21")]
abbrev zipWithIndex_mk := @zipIdx_mk

@[simp] theorem mk_zipWith_mk (f : α → β → γ) (a : Array α) (b : Array β)
      (ha : a.size = n) (hb : b.size = n) : zipWith f (Vector.mk a ha) (Vector.mk b hb) =
        Vector.mk (Array.zipWith f a b) (by simp [ha, hb]) := rfl

@[simp] theorem mk_zip_mk (a : Array α) (b : Array β) (ha : a.size = n) (hb : b.size = n) :
    zip (Vector.mk a ha) (Vector.mk b hb) = Vector.mk (Array.zip a b) (by simp [ha, hb]) := rfl

@[simp] theorem unzip_mk (a : Array (α × β)) (h : a.size = n) :
    (Vector.mk a h).unzip = (Vector.mk a.unzip.1 (by simp_all), Vector.mk a.unzip.2 (by simp_all)) := rfl

@[simp] theorem anyM_mk [Monad m] (p : α → m Bool) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).anyM p = a.anyM p := rfl

@[simp] theorem allM_mk [Monad m] (p : α → m Bool) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).allM p = a.allM p := rfl

@[simp] theorem any_mk (p : α → Bool) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).any p = a.any p := rfl

@[simp] theorem all_mk (p : α → Bool) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).all p = a.all p := rfl

@[simp] theorem countP_mk (p : α → Bool) (a : Array α) (h : a.size = n) :
    (Vector.mk a h).countP p = a.countP p := rfl

@[simp] theorem count_mk [BEq α] (a : Array α) (h : a.size = n) (b : α) :
    (Vector.mk a h).count b = a.count b := rfl

@[simp] theorem eq_mk : v = Vector.mk a h ↔ v.toArray = a := by
  cases v
  simp

@[simp] theorem mk_eq : Vector.mk a h = v ↔ a = v.toArray := by
  cases v
  simp

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

@[simp] theorem toArray_mapIdx (f : Nat → α → β) (a : Vector α n) :
    (a.mapIdx f).toArray = a.toArray.mapIdx f := rfl

@[simp] theorem toArray_mapFinIdx (f : (i : Nat) → α → (h : i < n) → β) (v : Vector α n) :
    (v.mapFinIdx f).toArray =
      v.toArray.mapFinIdx (fun i a h => f i a (by simpa [v.size_toArray] using h)) :=
  rfl

theorem toArray_mapM_go [Monad m] [LawfulMonad m] (f : α → m β) (v : Vector α n) (i h r) :
    toArray <$> mapM.go f v i h r = Array.mapM.map f v.toArray i r.toArray := by
  unfold mapM.go
  unfold Array.mapM.map
  simp only [v.size_toArray, getElem_toArray]
  split
  · simp only [map_bind]
    congr
    funext b
    rw [toArray_mapM_go]
    rfl
  · simp

@[simp] theorem toArray_mapM [Monad m] [LawfulMonad m] (f : α → m β) (a : Vector α n) :
    toArray <$> a.mapM f = a.toArray.mapM f := by
  rcases a with ⟨a, rfl⟩
  unfold mapM
  rw [toArray_mapM_go]
  rfl

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

@[simp] theorem toArray_zipIdx (a : Vector α n) (k : Nat := 0) :
    (a.zipIdx k).toArray = a.toArray.zipIdx k := rfl

@[simp] theorem toArray_zipWith (f : α → β → γ) (a : Vector α n) (b : Vector β n) :
    (Vector.zipWith f a b).toArray = Array.zipWith f a.toArray b.toArray := rfl

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

@[simp] theorem countP_toArray (p : α → Bool) (v : Vector α n) :
    v.toArray.countP p = v.countP p := by
  cases v
  simp

@[simp] theorem count_toArray [BEq α] (a : α) (v : Vector α n) :
    v.toArray.count a = v.count a := by
  cases v
  simp

@[simp] theorem toArray_mkVector : (mkVector n a).toArray = mkArray n a := rfl

@[simp] theorem toArray_inj {v w : Vector α n} : v.toArray = w.toArray ↔ v = w := by
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

/-! ### toList -/

theorem toArray_toList (a : Vector α n) : a.toArray.toList = a.toList := rfl

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

theorem toList_mapIdx (f : Nat → α → β) (a : Vector α n) :
    (a.mapIdx f).toList = a.toList.mapIdx f := by simp

theorem toList_mapFinIdx (f : (i : Nat) → α → (h : i < n) → β) (v : Vector α n) :
    (v.mapFinIdx f).toList =
      v.toList.mapFinIdx (fun i a h => f i a (by simpa [v.size_toArray] using h)) := by
  simp

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
    (Vector.zipWith f a b).toArray = Array.zipWith f a.toArray b.toArray := rfl

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

@[simp] theorem countP_toList (p : α → Bool) (v : Vector α n) :
    v.toList.countP p = v.countP p := by
  cases v
  simp

@[simp] theorem count_toList [BEq α] (a : α) (v : Vector α n) :
    v.toList.count a = v.count a := by
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

/-! ### cast -/

@[simp] theorem getElem_cast (a : Vector α n) (h : n = m) (i : Nat) (hi : i < m) :
    (a.cast h)[i] = a[i] := by
  cases a
  simp

@[simp] theorem getElem?_cast {l : Vector α n} {m : Nat} {w : n = m} {i : Nat} :
    (l.cast w)[i]? = l[i]? := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem mem_cast {a : α} {l : Vector α n} {m : Nat} {w : n = m} :
    a ∈ l.cast w ↔ a ∈ l := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem cast_cast {l : Vector α n} {w : n = m} {w' : m = k} :
    (l.cast w).cast w' = l.cast (w.trans w') := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem cast_rfl {l : Vector α n} : l.cast rfl = l := by
  rcases l with ⟨l, rfl⟩
  simp

/-! ### mkVector -/

@[simp] theorem mkVector_zero : mkVector 0 a = #v[] := rfl

theorem mkVector_succ : mkVector (n + 1) a = (mkVector n a).push a := by
  simp [mkVector, Array.mkArray_succ]

@[simp] theorem mkVector_inj : mkVector n a = mkVector n b ↔ n = 0 ∨ a = b := by
  simp [← toArray_inj, toArray_mkVector, Array.mkArray_inj]

@[simp] theorem _root_.Array.mk_mkArray (a : α) (n : Nat) (h : (mkArray n a).size = m) :
    mk (Array.mkArray n a) h = (mkVector n a).cast (by simpa using h) := rfl

theorem mkVector_eq_mk_mkArray (a : α) (n : Nat) :
    mkVector n a = mk (mkArray n a) (by simp) := by
  simp

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

theorem mem_of_getElem {l : Vector α n} {i : Nat} {h} {a : α} (e : l[i] = a) : a ∈ l := by
  subst e
  simp

theorem mem_of_getElem? {l : Vector α n} {i : Nat} {a : α} (e : l[i]? = some a) : a ∈ l :=
  let ⟨_, e⟩ := getElem?_eq_some_iff.1 e; e ▸ getElem_mem ..

theorem mem_of_back? {xs : Vector α n} {a : α} (h : xs.back? = some a) : a ∈ xs := by
  cases xs
  simpa using Array.mem_of_back? (by simpa using h)

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
        obtain ⟨hs, hi⟩ := Array.isEqv_iff_rel.mp h
        ext i h
        · simpa using hi _ (by omega)
      · rintro ⟨a, ha⟩
        simpa using Array.isEqv_self_beq ..

/-! ### isEqv -/

@[simp] theorem isEqv_eq [DecidableEq α] {l₁ l₂ : Vector α n} : l₁.isEqv l₂ (· == ·) = (l₁ = l₂) := by
  cases l₁
  cases l₂
  simp

/-! ### map -/

@[simp] theorem getElem_map (f : α → β) (a : Vector α n) (i : Nat) (hi : i < n) :
    (a.map f)[i] = f a[i] := by
  cases a
  simp

@[simp] theorem getElem?_map (f : α → β) (a : Vector α n) (i : Nat) :
    (a.map f)[i]? = a[i]?.map f := by
  cases a
  simp

/-- The empty vector maps to the empty vector. -/
@[simp]
theorem map_empty (f : α → β) : map f #v[] = #v[] := by
  rw [map, mk.injEq]
  exact Array.map_empty f

@[simp] theorem map_push {f : α → β} {as : Vector α n} {x : α} :
    (as.push x).map f = (as.map f).push (f x) := by
  cases as
  simp

@[simp] theorem map_id_fun : map (n := n) (id : α → α) = id := by
  funext l
  induction l <;> simp_all

/-- `map_id_fun'` differs from `map_id_fun` by representing the identity function as a lambda, rather than `id`. -/
@[simp] theorem map_id_fun' : map (n := n) (fun (a : α) => a) = id := map_id_fun

-- This is not a `@[simp]` lemma because `map_id_fun` will apply.
theorem map_id (l : Vector α n) : map (id : α → α) l = l := by
  cases l <;> simp_all

/-- `map_id'` differs from `map_id` by representing the identity function as a lambda, rather than `id`. -/
-- This is not a `@[simp]` lemma because `map_id_fun'` will apply.
theorem map_id' (l : Vector α n) : map (fun (a : α) => a) l = l := map_id l

/-- Variant of `map_id`, with a side condition that the function is pointwise the identity. -/
theorem map_id'' {f : α → α} (h : ∀ x, f x = x) (l : Vector α n) : map f l = l := by
  simp [show f = id from funext h]

theorem map_singleton (f : α → β) (a : α) : map f #v[a] = #v[f a] := rfl

-- We use a lower priority here as there are more specific lemmas in downstream libraries
-- which should be able to fire first.
@[simp 500] theorem mem_map {f : α → β} {l : Vector α n} : b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b := by
  cases l
  simp

theorem exists_of_mem_map (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b := mem_map.1 h

theorem mem_map_of_mem (f : α → β) (h : a ∈ l) : f a ∈ map f l := mem_map.2 ⟨_, h, rfl⟩

theorem forall_mem_map {f : α → β} {l : Vector α n} {P : β → Prop} :
    (∀ (i) (_ : i ∈ l.map f), P i) ↔ ∀ (j) (_ : j ∈ l), P (f j) := by
  simp

@[simp] theorem map_inj_left {f g : α → β} : map f l = map g l ↔ ∀ a ∈ l, f a = g a := by
  cases l <;> simp_all

theorem map_inj_right {f : α → β} (w : ∀ x y, f x = f y → x = y) : map f l = map f l' ↔ l = l' := by
  cases l
  cases l'
  simp [Array.map_inj_right w]

theorem map_congr_left (h : ∀ a ∈ l, f a = g a) : map f l = map g l :=
  map_inj_left.2 h

theorem map_inj [NeZero n] : map (n := n) f = map g ↔ f = g := by
  constructor
  · intro h
    ext a
    replace h := congrFun h (mkVector n a)
    simp only [mkVector, map_mk, mk.injEq, Array.map_inj_left, Array.mem_mkArray,  and_imp,
      forall_eq_apply_imp_iff] at h
    exact h (NeZero.ne n)
  · intro h; subst h; rfl

theorem map_eq_push_iff {f : α → β} {l : Vector α (n + 1)} {l₂ : Vector β n} {b : β} :
    map f l = l₂.push b ↔ ∃ l₁ a, l = l₁.push a ∧ map f l₁ = l₂ ∧ f a = b := by
  rcases l with ⟨l, h⟩
  rcases l₂ with ⟨l₂, rfl⟩
  simp only [map_mk, push_mk, mk.injEq, Array.map_eq_push_iff]
  constructor
  · rintro ⟨l₁, a, rfl, rfl, rfl⟩
    refine ⟨⟨l₁, by simp⟩, a, by simp⟩
  · rintro ⟨l₁, a, h₁, h₂, rfl⟩
    refine ⟨l₁.toArray, a, by simp_all⟩

@[simp] theorem map_eq_singleton_iff {f : α → β} {l : Vector α 1} {b : β} :
    map f l = #v[b] ↔ ∃ a, l = #v[a] ∧ f a = b := by
  cases l
  simp

theorem map_eq_map_iff {f g : α → β} {l : Vector α n} :
    map f l = map g l ↔ ∀ a ∈ l, f a = g a := by
  cases l <;> simp_all

theorem map_eq_iff {f : α → β} {l : Vector α n} {l' : Vector β n} :
    map f l = l' ↔ ∀ i (h : i < n), l'[i] = f l[i] := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', h'⟩
  simp only [map_mk, eq_mk, Array.map_eq_iff, getElem_mk]
  constructor
  · intro w i h
    simpa [h, h'] using w i
  · intro w i
    if h : i < l.size then
      simpa [h, h'] using w i h
    else
      rw [getElem?_neg, getElem?_neg, Option.map_none'] <;> omega

@[simp] theorem map_set {f : α → β} {l : Vector α n} {i : Nat} {h : i < n} {a : α} :
    (l.set i a).map f = (l.map f).set i (f a) (by simpa using h) := by
  cases l
  simp

@[simp] theorem map_setIfInBounds {f : α → β} {l : Vector α n} {i : Nat} {a : α} :
    (l.setIfInBounds i a).map f = (l.map f).setIfInBounds i (f a) := by
  cases l
  simp

@[simp] theorem map_pop {f : α → β} {l : Vector α n} : l.pop.map f = (l.map f).pop := by
  cases l
  simp

@[simp] theorem back?_map {f : α → β} {l : Vector α n} : (l.map f).back? = l.back?.map f := by
  cases l
  simp

@[simp] theorem map_map {f : α → β} {g : β → γ} {as : Vector α n} :
    (as.map f).map g = as.map (g ∘ f) := by
  cases as
  simp

/--
Use this as `induction ass using vector₂_induction` on a hypothesis of the form `ass : Vector (Vector α n) m`.
The hypothesis `ass` will be replaced with a hypothesis `ass : Array (Array α)`
along with additional hypotheses `h₁ : ass.size = m` and `h₂ : ∀ xs ∈ ass, xs.size = n`.
Appearances of the original `ass` in the goal will be replaced with
`Vector.mk (xss.attach.map (fun ⟨xs, m⟩ => Vector.mk xs ⋯)) ⋯`.
-/
-- We can't use `@[cases_eliminator]` here as
-- `Lean.Meta.getCustomEliminator?` only looks at the top-level constant.
theorem vector₂_induction (P : Vector (Vector α n) m → Prop)
    (of : ∀ (xss : Array (Array α)) (h₁ : xss.size = m) (h₂ : ∀ xs ∈ xss, xs.size = n),
      P (mk (xss.attach.map (fun ⟨xs, m⟩ => mk xs (h₂ xs m))) (by simpa using h₁)))
    (ass : Vector (Vector α n) m) : P ass := by
  specialize of (ass.map toArray).toArray (by simp) (by simp)
  simpa [Array.map_attach, Array.pmap_map] using of

/--
Use this as `induction ass using vector₃_induction` on a hypothesis of the form `ass : Vector (Vector (Vector α n) m) k`.
The hypothesis `ass` will be replaced with a hypothesis `ass : Array (Array (Array α))`
along with additional hypotheses `h₁ : ass.size = k`, `h₂ : ∀ xs ∈ ass, xs.size = m`,
and `h₃ : ∀ xs ∈ ass, ∀ x ∈ xs, x.size = n`.
Appearances of the original `ass` in the goal will be replaced with
`Vector.mk (xss.attach.map (fun ⟨xs, m⟩ => Vector.mk (xs.attach.map (fun ⟨x, m'⟩ => Vector.mk x ⋯)) ⋯)) ⋯`.
-/
theorem vector₃_induction (P : Vector (Vector (Vector α n) m) k → Prop)
    (of : ∀ (xss : Array (Array (Array α))) (h₁ : xss.size = k) (h₂ : ∀ xs ∈ xss, xs.size = m)
      (h₃ : ∀ xs ∈ xss, ∀ x ∈ xs, x.size = n),
      P (mk (xss.attach.map (fun ⟨xs, m⟩ =>
        mk (xs.attach.map (fun ⟨x, m'⟩ =>
          mk x (h₃ xs m x m'))) (by simpa using h₂ xs m))) (by simpa using h₁)))
    (ass : Vector (Vector (Vector α n) m) k) : P ass := by
  specialize of (ass.map (fun as => (as.map toArray).toArray)).toArray (by simp) (by simp) (by simp)
  simpa [Array.map_attach, Array.pmap_map] using of

/-! ### singleton -/

@[simp] theorem singleton_def (v : α) : Vector.singleton v = #v[v] := rfl

/-! ### append -/

@[simp] theorem append_push {as : Vector α n} {bs : Vector α m} {a : α} :
    as ++ bs.push a = (as ++ bs).push a := by
  cases as
  cases bs
  simp

theorem singleton_eq_toVector_singleton (a : α) : #v[a] = #[a].toVector := rfl

@[simp] theorem mem_append {a : α} {s : Vector α n} {t : Vector α m} :
    a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := by
  cases s
  cases t
  simp

theorem mem_append_left {a : α} {s : Vector α n} (t : Vector α m) (h : a ∈ s) : a ∈ s ++ t :=
  mem_append.2 (Or.inl h)

theorem mem_append_right {a : α} (s : Vector α n) {t : Vector α m} (h : a ∈ t) : a ∈ s ++ t :=
  mem_append.2 (Or.inr h)

theorem not_mem_append {a : α} {s : Vector α n} {t : Vector α m} (h₁ : a ∉ s) (h₂ : a ∉ t) :
    a ∉ s ++ t :=
  mt mem_append.1 $ not_or.mpr ⟨h₁, h₂⟩

/--
See also `eq_push_append_of_mem`, which proves a stronger version
in which the initial array must not contain the element.
-/
theorem append_of_mem {a : α} {l : Vector α n} (h : a ∈ l) :
    ∃ (m k : Nat) (w : m + 1 + k = n) (s : Vector α m) (t : Vector α k),
      l = (s.push a ++ t).cast w := by
  rcases l with ⟨l, rfl⟩
  obtain ⟨s, t, rfl⟩ := Array.append_of_mem (by simpa using h)
  refine ⟨_, _, by simp, s.toVector, t.toVector, by simp_all⟩

theorem mem_iff_append {a : α} {l : Vector α n} :
    a ∈ l ↔ ∃ (m k : Nat) (w : m + 1 + k = n) (s : Vector α m) (t : Vector α k),
      l = (s.push a ++ t).cast w :=
  ⟨append_of_mem, by rintro ⟨m, k, rfl, s, t, rfl⟩; simp⟩

theorem forall_mem_append {p : α → Prop} {l₁ : Vector α n} {l₂ : Vector α m} :
    (∀ (x) (_ : x ∈ l₁ ++ l₂), p x) ↔ (∀ (x) (_ : x ∈ l₁), p x) ∧ (∀ (x) (_ : x ∈ l₂), p x) := by
  simp only [mem_append, or_imp, forall_and]

theorem empty_append (as : Vector α n) : (#v[] : Vector α 0) ++ as = as.cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp

theorem append_empty (as : Vector α n) : as ++ (#v[] : Vector α 0) = as := by
  rw [← toArray_inj, toArray_append, Array.append_empty]

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

theorem getElem?_append_left {as : Vector α n} {bs : Vector α m} {i : Nat} (hn : i < n) :
    (as ++ bs)[i]? = as[i]? := by
  have hn' : i < n + m := by omega
  simp_all [getElem?_eq_getElem, getElem_append]

theorem getElem?_append_right {as : Vector α n} {bs : Vector α m} {i : Nat} (h : n ≤ i) :
    (as ++ bs)[i]? = bs[i - n]? := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  simp [Array.getElem?_append_right, h]

theorem getElem?_append {as : Vector α n} {bs : Vector α m} {i : Nat} :
    (as ++ bs)[i]? = if i < n then as[i]? else bs[i - n]? := by
  split <;> rename_i h
  · exact getElem?_append_left h
  · exact getElem?_append_right (by simpa using h)

/-- Variant of `getElem_append_left` useful for rewriting from the small array to the big array. -/
theorem getElem_append_left' (l₁ : Vector α m) {l₂ : Vector α n} {i : Nat} (hi : i < m) :
    l₁[i] = (l₁ ++ l₂)[i] := by
  rw [getElem_append_left] <;> simp

/-- Variant of `getElem_append_right` useful for rewriting from the small array to the big array. -/
theorem getElem_append_right' (l₁ : Vector α m) {l₂ : Vector α n} {i : Nat} (hi : i < n) :
    l₂[i] = (l₁ ++ l₂)[i + m] := by
  rw [getElem_append_right] <;> simp [*, Nat.le_add_left]

theorem getElem_of_append {l : Vector α n} {l₁ : Vector α m} {l₂ : Vector α k}
    (w : m + 1 + k = n) (eq : l = (l₁.push a ++ l₂).cast w) :
    l[m] = a := Option.some.inj <| by
  rw [← getElem?_eq_getElem, eq, getElem?_cast, getElem?_append_left (by simp)]
  simp

@[simp] theorem append_singleton {a : α} {as : Vector α n} : as ++ #v[a] = as.push a := by
  cases as
  simp

theorem append_inj {s₁ s₂ : Vector α n} {t₁ t₂ : Vector α m} (h : s₁ ++ t₁ = s₂ ++ t₂) :
    s₁ = s₂ ∧ t₁ = t₂ := by
  rcases s₁ with ⟨s₁, rfl⟩
  rcases s₂ with ⟨s₂, hs⟩
  rcases t₁ with ⟨t₁, rfl⟩
  rcases t₂ with ⟨t₂, ht⟩
  simpa using Array.append_inj (by simpa using h) (by omega)

theorem append_inj_right {s₁ s₂ : Vector α n} {t₁ t₂ : Vector α m}
    (h : s₁ ++ t₁ = s₂ ++ t₂) : t₁ = t₂ :=
  (append_inj h).right

theorem append_inj_left {s₁ s₂ : Vector α n} {t₁ t₂ : Vector α m}
    (h : s₁ ++ t₁ = s₂ ++ t₂) : s₁ = s₂ :=
  (append_inj h).left

theorem append_right_inj {t₁ t₂ : Vector α m} (s : Vector α n) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  ⟨fun h => append_inj_right h, congrArg _⟩

theorem append_left_inj {s₁ s₂ : Vector α n} (t : Vector α m) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  ⟨fun h => append_inj_left h, congrArg (· ++ _)⟩

theorem append_eq_append_iff {a : Vector α n} {b : Vector α m} {c : Vector α k} {d : Vector α l}
    (w : k + l = n + m) :
    a ++ b = (c ++ d).cast w ↔
      if h : n ≤ k then
        ∃ a' : Vector α (k - n), c = (a ++ a').cast (by omega) ∧ b = (a' ++ d).cast (by omega)
      else
        ∃ c' : Vector α (n - k), a = (c ++ c').cast (by omega) ∧ d = (c' ++ b).cast (by omega) := by
  rcases a with ⟨a, rfl⟩
  rcases b with ⟨b, rfl⟩
  rcases c with ⟨c, rfl⟩
  rcases d with ⟨d, rfl⟩
  simp only [mk_append_mk, Array.append_eq_append_iff, mk_eq, toArray_cast]
  constructor
  · rintro (⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩)
    · rw [dif_pos (by simp)]
      exact ⟨a'.toVector.cast (by simp; omega), by simp⟩
    · split <;> rename_i h
      · have hc : c'.size = 0 := by simp at h; omega
        simp at hc
        exact ⟨#v[].cast (by simp; omega), by simp_all⟩
      · exact ⟨c'.toVector.cast (by simp; omega), by simp⟩
  · split <;> rename_i h
    · rintro ⟨a', hc, rfl⟩
      left
      refine ⟨a'.toArray, hc, rfl⟩
    · rintro ⟨c', ha, rfl⟩
      right
      refine ⟨c'.toArray, ha, rfl⟩

theorem set_append {s : Vector α n} {t : Vector α m} {i : Nat} {x : α} (h : i < n + m) :
    (s ++ t).set i x =
      if h' : i < n then
        s.set i x ++ t
      else
        s ++ t.set (i - n) x := by
  rcases s with ⟨s, rfl⟩
  rcases t with ⟨t, rfl⟩
  simp only [mk_append_mk, set_mk, Array.set_append]
  split <;> simp

@[simp] theorem set_append_left {s : Vector α n} {t : Vector α m} {i : Nat} {x : α} (h : i < n) :
    (s ++ t).set i x = s.set i x ++ t := by
  simp [set_append, h]

@[simp] theorem set_append_right {s : Vector α n} {t : Vector α m} {i : Nat} {x : α}
    (h' : i < n + m) (h : n ≤ i) :
    (s ++ t).set i x = s ++ t.set (i - n) x := by
  rw [set_append, dif_neg (by omega)]

theorem setIfInBounds_append {s : Vector α n} {t : Vector α m} {i : Nat} {x : α} :
    (s ++ t).setIfInBounds i x =
      if i < n then
        s.setIfInBounds i x ++ t
      else
        s ++ t.setIfInBounds (i - n) x := by
  rcases s with ⟨s, rfl⟩
  rcases t with ⟨t, rfl⟩
  simp only [mk_append_mk, setIfInBounds_mk, Array.setIfInBounds_append]
  split <;> simp

@[simp] theorem setIfInBounds_append_left {s : Vector α n} {t : Vector α m} {i : Nat} {x : α} (h : i < n) :
    (s ++ t).setIfInBounds i x = s.setIfInBounds i x ++ t := by
  simp [setIfInBounds_append, h]

@[simp] theorem setIfInBounds_append_right {s : Vector α n} {t : Vector α m} {i : Nat} {x : α}
    (h : n ≤ i) :
    (s ++ t).setIfInBounds i x = s ++ t.setIfInBounds (i - n) x := by
  rw [setIfInBounds_append, if_neg (by omega)]

@[simp] theorem map_append (f : α → β) (l₁ : Vector α n) (l₂ : Vector α m) :
    map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  rcases l₁ with ⟨l₁, rfl⟩
  rcases l₂ with ⟨l₂, rfl⟩
  simp

theorem map_eq_append_iff {f : α → β} :
    map f l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = L₁ ∧ map f l₂ = L₂ := by
  rcases l with ⟨l, h⟩
  rcases L₁ with ⟨L₁, rfl⟩
  rcases L₂ with ⟨L₂, rfl⟩
  simp only [map_mk, mk_append_mk, eq_mk, Array.map_eq_append_iff, mk_eq, toArray_append,
    toArray_map]
  constructor
  · rintro ⟨l₁, l₂, rfl, rfl, rfl⟩
    exact ⟨l₁.toVector.cast (by simp), l₂.toVector.cast (by simp), by simp⟩
  · rintro ⟨⟨l₁⟩, ⟨l₂⟩, rfl, h₁, h₂⟩
    exact ⟨l₁, l₂, by simp_all⟩

theorem append_eq_map_iff {f : α → β} :
    L₁ ++ L₂ = map f l ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = L₁ ∧ map f l₂ = L₂ := by
  rw [eq_comm, map_eq_append_iff]

/-! ### flatten -/

@[simp] theorem flatten_mk (L : Array (Vector α n)) (h : L.size = m) :
    (mk L h).flatten =
      mk (L.map toArray).flatten (by simp [Function.comp_def, Array.map_const', h]) := by
  simp [flatten]

@[simp] theorem getElem_flatten (l : Vector (Vector β m) n) (i : Nat) (hi : i < n * m) :
    l.flatten[i] =
      haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]
      haveI : i % m < m := Nat.mod_lt _ (Nat.pos_of_lt_mul_left hi)
      l[i / m][i % m] := by
  rcases l with ⟨⟨l⟩, rfl⟩
  simp only [flatten_mk, List.map_toArray, getElem_mk, List.getElem_toArray, Array.flatten_toArray]
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    simp only [List.map_cons, List.map_map, List.flatten_cons]
    by_cases h : i < m
    · rw [List.getElem_append_left (by simpa)]
      have h₁ : i / m = 0 := Nat.div_eq_of_lt h
      have h₂ : i % m = i := Nat.mod_eq_of_lt h
      simp [h₁, h₂]
    · have h₁ : a.toList.length ≤ i := by simp; omega
      rw [List.getElem_append_right h₁]
      simp only [Array.length_toList, size_toArray]
      specialize ih (i - m) (by simp_all [Nat.add_one_mul]; omega)
      have h₂ : i / m = (i - m) / m + 1 := by
        conv => lhs; rw [show i = i - m + m by omega]
        rw [Nat.add_div_right]
        exact Nat.pos_of_lt_mul_left hi
      simp only [Array.length_toList, size_toArray] at h₁
      have h₃ : (i - m) % m = i % m := (Nat.mod_eq_sub_mod h₁).symm
      simp_all

theorem getElem?_flatten (l : Vector (Vector β m) n) (i : Nat) :
    l.flatten[i]? =
      if hi : i < n * m then
        haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]
        haveI : i % m < m := Nat.mod_lt _ (Nat.pos_of_lt_mul_left hi)
        some l[i / m][i % m]
      else
        none := by
  simp [getElem?_def]

@[simp] theorem flatten_singleton (l : Vector α n) : #v[l].flatten = l.cast (by simp) := by
  simp [flatten]

theorem mem_flatten {L : Vector (Vector α n) m} : a ∈ L.flatten ↔ ∃ l, l ∈ L ∧ a ∈ l := by
  rcases L with ⟨L, rfl⟩
  simp [Array.mem_flatten]
  constructor
  · rintro ⟨_, ⟨l, h₁, rfl⟩, h₂⟩
    exact ⟨l, h₁, by simpa using h₂⟩
  · rintro ⟨l, h₁, h₂⟩
    exact ⟨l.toArray, ⟨l, h₁, rfl⟩, by simpa using h₂⟩

theorem exists_of_mem_flatten : a ∈ flatten L → ∃ l, l ∈ L ∧ a ∈ l := mem_flatten.1

theorem mem_flatten_of_mem (lL : l ∈ L) (al : a ∈ l) : a ∈ flatten L := mem_flatten.2 ⟨l, lL, al⟩

theorem forall_mem_flatten {p : α → Prop} {L : Vector (Vector α n) m} :
    (∀ (x) (_ : x ∈ flatten L), p x) ↔ ∀ (l) (_ : l ∈ L) (x) (_ : x ∈ l), p x := by
  simp only [mem_flatten, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

@[simp] theorem map_flatten (f : α → β) (L : Vector (Vector α n) m) :
    (flatten L).map f = (map (map f) L).flatten := by
  induction L using vector₂_induction with
  | of xss h₁ h₂ => simp

@[simp] theorem flatten_append (L₁ : Vector (Vector α n) m₁) (L₂ : Vector (Vector α n) m₂) :
    flatten (L₁ ++ L₂) = (flatten L₁ ++ flatten L₂).cast (by simp [Nat.add_mul]) := by
  induction L₁ using vector₂_induction
  induction L₂ using vector₂_induction
  simp

theorem flatten_push (L : Vector (Vector α n) m) (l : Vector α n) :
    flatten (L.push l) = (flatten L ++ l).cast (by simp [Nat.add_mul]) := by
  induction L using vector₂_induction
  rcases l with ⟨l⟩
  simp [Array.flatten_push]

theorem flatten_flatten {L : Vector (Vector (Vector α n) m) k} :
    flatten (flatten L) = (flatten (map flatten L)).cast (by simp [Nat.mul_assoc]) := by
  induction L using vector₃_induction with
  | of xss h₁ h₂ h₃ =>
    -- simp [Array.flatten_flatten] -- FIXME: `simp` produces a bad proof here!
    simp [Array.map_attach, Array.flatten_flatten, Array.map_pmap]

/-- Two vectors of constant length vectors are equal iff their flattens coincide. -/
theorem eq_iff_flatten_eq {L L' : Vector (Vector α n) m} :
    L = L' ↔ L.flatten = L'.flatten := by
  induction L using vector₂_induction with | of L h₁ h₂ =>
  induction L' using vector₂_induction with | of L' h₁' h₂' =>
  simp only [eq_mk, flatten_mk, Array.map_map, Function.comp_apply, Array.map_subtype,
    Array.unattach_attach, Array.map_id_fun', id_eq]
  constructor
  · intro h
    suffices L = L' by simp_all
    apply Array.ext_getElem?
    intro i
    replace h := congrArg (fun x => x[i]?.map (fun x => x.toArray)) h
    simpa [Option.map_pmap] using h
  · intro h
    have w : L.map Array.size = L'.map Array.size := by
      ext i h h'
      · simp_all
      · simp only [Array.getElem_map]
        rw [h₂ _ (by simp), h₂' _ (by simp)]
    have := Array.eq_iff_flatten_eq.mpr ⟨h, w⟩
    subst this
    rfl


/-! ### flatMap -/

@[simp] theorem flatMap_toArray (l : Vector α n) (f : α → Vector β m) :
    l.toArray.flatMap (fun a => (f a).toArray) = (l.flatMap f).toArray := by
  rcases l with ⟨l, rfl⟩
  simp

theorem flatMap_def (l : Vector α n) (f : α → Vector β m) : l.flatMap f = flatten (map f l) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.flatMap_def, Function.comp_def]

@[simp] theorem getElem_flatMap (l : Vector α n) (f : α → Vector β m) (i : Nat) (hi : i < n * m) :
    (l.flatMap f)[i] =
      haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]
      haveI : i % m < m := Nat.mod_lt _ (Nat.pos_of_lt_mul_left hi)
      (f (l[i / m]))[i % m] := by
  rw [flatMap_def, getElem_flatten, getElem_map]

theorem getElem?_flatMap (l : Vector α n) (f : α → Vector β m) (i : Nat) :
    (l.flatMap f)[i]? =
      if hi : i < n * m then
        haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]
        haveI : i % m < m := Nat.mod_lt _ (Nat.pos_of_lt_mul_left hi)
        some ((f (l[i / m]))[i % m])
      else
        none := by
  simp [getElem?_def]

@[simp] theorem flatMap_id (l : Vector (Vector α m) n) : l.flatMap id = l.flatten := by simp [flatMap_def]

@[simp] theorem flatMap_id' (l : Vector (Vector α m) n) : l.flatMap (fun a => a) = l.flatten := by simp [flatMap_def]

@[simp] theorem mem_flatMap {f : α → Vector β m} {b} {l : Vector α n} : b ∈ l.flatMap f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [flatMap_def, mem_flatten]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem exists_of_mem_flatMap {b : β} {l : Vector α n} {f : α → Vector β m} :
    b ∈ l.flatMap f → ∃ a, a ∈ l ∧ b ∈ f a := mem_flatMap.1

theorem mem_flatMap_of_mem {b : β} {l : Vector α n} {f : α → Vector β m} {a} (al : a ∈ l) (h : b ∈ f a) :
    b ∈ l.flatMap f := mem_flatMap.2 ⟨a, al, h⟩

theorem forall_mem_flatMap {p : β → Prop} {l : Vector α n} {f : α → Vector β m} :
    (∀ (x) (_ : x ∈ l.flatMap f), p x) ↔ ∀ (a) (_ : a ∈ l) (b) (_ : b ∈ f a), p b := by
  simp only [mem_flatMap, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

theorem flatMap_singleton (f : α → Vector β m) (x : α) : #v[x].flatMap f = (f x).cast (by simp) := by
  simp [flatMap_def]

@[simp] theorem flatMap_singleton' (l : Vector α n) : (l.flatMap fun x => #v[x]) = l.cast (by simp) := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem flatMap_append (xs ys : Vector α n) (f : α → Vector β m) :
    (xs ++ ys).flatMap f = (xs.flatMap f ++ ys.flatMap f).cast (by simp [Nat.add_mul]) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp [flatMap_def, flatten_append]

theorem flatMap_assoc {α β} (l : Vector α n) (f : α → Vector β m) (g : β → Vector γ k) :
    (l.flatMap f).flatMap g = (l.flatMap fun x => (f x).flatMap g).cast (by simp [Nat.mul_assoc]) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.flatMap_assoc]

theorem map_flatMap (f : β → γ) (g : α → Vector β m) (l : Vector α n) :
     (l.flatMap g).map f = l.flatMap fun a => (g a).map f := by
  rcases l with ⟨l, rfl⟩
  simp [Array.map_flatMap]

theorem flatMap_map (f : α → β) (g : β → Vector γ k) (l : Vector α n) :
     (map f l).flatMap g = l.flatMap (fun a => g (f a)) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.flatMap_map]

theorem map_eq_flatMap {α β} (f : α → β) (l : Vector α n) :
    map f l = (l.flatMap fun x => #v[f x]).cast (by simp) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.map_eq_flatMap]

/-! ### mkVector -/

@[simp] theorem mkVector_one : mkVector 1 a = #v[a] := rfl

/-- Variant of `mkVector_succ` that prepends `a` at the beginning of the vector. -/
theorem mkVector_succ' : mkVector (n + 1) a = (#v[a] ++ mkVector n a).cast (by omega) := by
  rw [← toArray_inj]
  simp [Array.mkArray_succ']

@[simp] theorem mem_mkVector {a b : α} {n} : b ∈ mkVector n a ↔ n ≠ 0 ∧ b = a := by
  unfold mkVector
  simp only [mem_mk]
  simp

theorem eq_of_mem_mkVector {a b : α} {n} (h : b ∈ mkVector n a) : b = a := (mem_mkVector.1 h).2

theorem forall_mem_mkVector {p : α → Prop} {a : α} {n} :
    (∀ b, b ∈ mkVector n a → p b) ↔ n = 0 ∨ p a := by
  cases n <;> simp [mem_mkVector]

@[simp] theorem getElem_mkVector (a : α) (n i : Nat) (h : i < n) : (mkVector n a)[i] = a := by
  rw [mkVector_eq_mk_mkArray, getElem_mk]
  simp

theorem getElem?_mkVector (a : α) (n i : Nat) : (mkVector n a)[i]? = if i < n then some a else none := by
  simp [getElem?_def]

@[simp] theorem getElem?_mkVector_of_lt {n : Nat} {m : Nat} (h : m < n) : (mkVector n a)[m]? = some a := by
  simp [getElem?_mkVector, h]

theorem eq_mkVector_of_mem {a : α} {l : Vector α n} (h : ∀ (b) (_ : b ∈ l), b = a) : l = mkVector n a := by
  rw [← toArray_inj]
  simpa using Array.eq_mkArray_of_mem (l := l.toArray) (by simpa using h)

theorem eq_mkVector_iff {a : α} {n} {l : Vector α n} :
    l = mkVector n a ↔ ∀ (b) (_ : b ∈ l), b = a := by
  rw [← toArray_inj]
  simpa using Array.eq_mkArray_iff (l := l.toArray) (n := n)

theorem map_eq_mkVector_iff {l : Vector α n} {f : α → β} {b : β} :
    l.map f = mkVector n b ↔ ∀ x ∈ l, f x = b := by
  simp [eq_mkVector_iff]

@[simp] theorem map_const (l : Vector α n) (b : β) : map (Function.const α b) l = mkVector n b :=
  map_eq_mkVector_iff.mpr fun _ _ => rfl

@[simp] theorem map_const_fun (x : β) : map (n := n) (Function.const α x) = fun _ => mkVector n x := by
  funext l
  simp

/-- Variant of `map_const` using a lambda rather than `Function.const`. -/
-- This can not be a `@[simp]` lemma because it would fire on every `List.map`.
theorem map_const' (l : Vector α n) (b : β) : map (fun _ => b) l = mkVector n b :=
  map_const l b

@[simp] theorem set_mkVector_self : (mkVector n a).set i a h = mkVector n a := by
  rw [← toArray_inj]
  simp

@[simp] theorem setIfInBounds_mkVector_self : (mkVector n a).setIfInBounds i a = mkVector n a := by
  rw [← toArray_inj]
  simp

@[simp] theorem mkVector_append_mkVector : mkVector n a ++ mkVector m a = mkVector (n + m) a := by
  rw [← toArray_inj]
  simp

theorem append_eq_mkVector_iff {l₁ : Vector α n} {l₂ : Vector α m} {a : α} :
    l₁ ++ l₂ = mkVector (n + m) a ↔ l₁ = mkVector n a ∧ l₂ = mkVector m a := by
  simp [← toArray_inj, Array.append_eq_mkArray_iff]

theorem mkVector_eq_append_iff {l₁ : Vector α n} {l₂ : Vector α m} {a : α} :
    mkVector (n + m) a = l₁ ++ l₂ ↔ l₁ = mkVector n a ∧ l₂ = mkVector m a := by
  rw [eq_comm, append_eq_mkVector_iff]

@[simp] theorem map_mkVector : (mkVector n a).map f = mkVector n (f a) := by
  rw [← toArray_inj]
  simp


@[simp] theorem flatten_mkVector_empty : (mkVector n (#v[] : Vector α 0)).flatten = #v[] := by
  rw [← toArray_inj]
  simp

@[simp] theorem flatten_mkVector_singleton : (mkVector n #v[a]).flatten = (mkVector n a).cast (by simp) := by
  ext i h
  simp [h]

@[simp] theorem flatten_mkVector_mkVector : (mkVector n (mkVector m a)).flatten = mkVector (n * m) a := by
  ext i h
  simp [h]

theorem flatMap_mkArray {β} (f : α → Vector β m) : (mkVector n a).flatMap f = (mkVector n (f a)).flatten := by
  ext i h
  simp [h]

@[simp] theorem sum_mkArray_nat (n : Nat) (a : Nat) : (mkVector n a).sum = n * a := by
  simp [toArray_mkVector]

/-! ### reverse -/

@[simp] theorem reverse_push (as : Vector α n) (a : α) :
    (as.push a).reverse = (#v[a] ++ as.reverse).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp [Array.reverse_push]

@[simp] theorem mem_reverse {x : α} {as : Vector α n} : x ∈ as.reverse ↔ x ∈ as := by
  cases as
  simp

@[simp] theorem getElem_reverse (a : Vector α n) (i : Nat) (hi : i < n) :
    (a.reverse)[i] = a[n - 1 - i] := by
  rcases a with ⟨a, rfl⟩
  simp

/-- Variant of `getElem?_reverse` with a hypothesis giving the linear relation between the indices. -/
theorem getElem?_reverse' {l : Vector α n} (i j) (h : i + j + 1 = n) : l.reverse[i]? = l[j]? := by
  rcases l with ⟨l, rfl⟩
  simpa using Array.getElem?_reverse' i j h

@[simp]
theorem getElem?_reverse {l : Vector α n} {i} (h : i < n) :
    l.reverse[i]? = l[n - 1 - i]? := by
  cases l
  simp_all

@[simp] theorem reverse_reverse (as : Vector α n) : as.reverse.reverse = as := by
  rcases as with ⟨as, rfl⟩
  simp [Array.reverse_reverse]

theorem reverse_eq_iff {as bs : Vector α n} : as.reverse = bs ↔ as = bs.reverse := by
  constructor <;> (rintro rfl; simp)

@[simp] theorem reverse_inj {xs ys : Vector α n} : xs.reverse = ys.reverse ↔ xs = ys := by
  simp [reverse_eq_iff]

@[simp] theorem reverse_eq_push_iff {xs : Vector α (n + 1)} {ys : Vector α n} {a : α} :
    xs.reverse = ys.push a ↔ xs = (#v[a] ++ ys.reverse).cast (by omega) := by
  rcases xs with ⟨xs, h⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.reverse_eq_push_iff]

@[simp] theorem map_reverse (f : α → β) (l : Vector α n) : l.reverse.map f = (l.map f).reverse := by
  rcases l with ⟨l, rfl⟩
  simp [Array.map_reverse]

@[simp] theorem reverse_append (as : Vector α n) (bs : Vector α m) :
    (as ++ bs).reverse = (bs.reverse ++ as.reverse).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  simp [Array.reverse_append]

@[simp] theorem reverse_eq_append_iff {xs : Vector α (n + m)} {ys : Vector α n} {zs : Vector α m} :
    xs.reverse = ys ++ zs ↔ xs = (zs.reverse ++ ys.reverse).cast (by omega) := by
  cases xs
  cases ys
  cases zs
  simp

/-- Reversing a flatten is the same as reversing the order of parts and reversing all parts. -/
theorem reverse_flatten (L : Vector (Vector α m) n) :
    L.flatten.reverse = (L.map reverse).reverse.flatten := by
  cases L using vector₂_induction
  simp [Array.reverse_flatten]

/-- Flattening a reverse is the same as reversing all parts and reversing the flattened result. -/
theorem flatten_reverse (L : Vector (Vector α m) n) :
    L.reverse.flatten = (L.map reverse).flatten.reverse := by
  cases L using vector₂_induction
  simp [Array.flatten_reverse]

theorem reverse_flatMap {β} (l : Vector α n) (f : α → Vector β m) :
    (l.flatMap f).reverse = l.reverse.flatMap (reverse ∘ f) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.reverse_flatMap, Function.comp_def]

theorem flatMap_reverse {β} (l : Vector α n) (f : α → Vector β m) :
    (l.reverse.flatMap f) = (l.flatMap (reverse ∘ f)).reverse := by
  rcases l with ⟨l, rfl⟩
  simp [Array.flatMap_reverse, Function.comp_def]

@[simp] theorem reverse_mkVector (n) (a : α) : reverse (mkVector n a) = mkVector n a := by
  rw [← toArray_inj]
  simp

/-! ### extract -/

@[simp] theorem getElem_extract {as : Vector α n} {start stop : Nat}
    (h : i < min stop n - start) :
    (as.extract start stop)[i] = as[start + i] := by
  rcases as with ⟨as, rfl⟩
  simp

theorem getElem?_extract {as : Vector α n} {start stop : Nat} :
    (as.extract start stop)[i]? = if i < min stop as.size - start then as[start + i]? else none := by
  rcases as with ⟨as, rfl⟩
  simp [Array.getElem?_extract]

@[simp] theorem extract_size (as : Vector α n) : as.extract 0 n = as.cast (by simp) := by
  rcases as with ⟨as, rfl⟩
  simp

theorem extract_empty (start stop : Nat) :
    (#v[] : Vector α 0).extract start stop = #v[].cast (by simp) := by
  simp

/-! ### foldlM and foldrM -/

@[simp] theorem foldlM_append [Monad m] [LawfulMonad m] (f : β → α → m β) (b) (l : Vector α n) (l' : Vector α k) :
    (l ++ l').foldlM f b = l.foldlM f b >>= l'.foldlM f := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', rfl⟩
  simp

@[simp] theorem foldlM_empty [Monad m] (f : β → α → m β) (init : β) :
    foldlM f init #v[] = return init := by
  simp [foldlM]

@[simp] theorem foldrM_empty [Monad m] (f : α → β → m β) (init : β) :
    foldrM f init #v[] = return init := by
  simp [foldrM]

@[simp] theorem foldlM_push [Monad m] [LawfulMonad m] (l : Vector α n) (a : α) (f : β → α → m β) (b) :
    (l.push a).foldlM f b = l.foldlM f b >>= fun b => f b a := by
  rcases l with ⟨l, rfl⟩
  simp

theorem foldl_eq_foldlM (f : β → α → β) (b) (l : Vector α n) :
    l.foldl f b = l.foldlM (m := Id) f b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldl_eq_foldlM]

theorem foldr_eq_foldrM (f : α → β → β) (b) (l : Vector α n) :
    l.foldr f b = l.foldrM (m := Id) f b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldr_eq_foldrM]

@[simp] theorem id_run_foldlM (f : β → α → Id β) (b) (l : Vector α n) :
    Id.run (l.foldlM f b) = l.foldl f b := (foldl_eq_foldlM f b l).symm

@[simp] theorem id_run_foldrM (f : α → β → Id β) (b) (l : Vector α n) :
    Id.run (l.foldrM f b) = l.foldr f b := (foldr_eq_foldrM f b l).symm

@[simp] theorem foldlM_reverse [Monad m] (l : Vector α n) (f : β → α → m β) (b) :
    l.reverse.foldlM f b = l.foldrM (fun x y => f y x) b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldlM_reverse]

@[simp] theorem foldrM_reverse [Monad m] (l : Vector α n) (f : α → β → m β) (b) :
    l.reverse.foldrM f b = l.foldlM (fun x y => f y x) b := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem foldrM_push [Monad m] (f : α → β → m β) (init : β) (arr : Vector α n) (a : α) :
    (arr.push a).foldrM f init = f a init >>= arr.foldrM f := by
  rcases arr with ⟨arr, rfl⟩
  simp [Array.foldrM_push]

/-! ### foldl / foldr -/

@[congr]
theorem foldl_congr {as bs : Vector α n} (h₀ : as = bs) {f g : β → α → β} (h₁ : f = g)
     {a b : β} (h₂ : a = b) :
    as.foldl f a = bs.foldl g b := by
  congr

@[congr]
theorem foldr_congr {as bs : Vector α n} (h₀ : as = bs) {f g : α → β → β} (h₁ : f = g)
     {a b : β} (h₂ : a = b) :
    as.foldr f a = bs.foldr g b := by
  congr

@[simp] theorem foldr_push (f : α → β → β) (init : β) (arr : Vector α n) (a : α) :
    (arr.push a).foldr f init = arr.foldr f (f a init) := by
  rcases arr with ⟨arr, rfl⟩
  simp [Array.foldr_push]

theorem foldl_map (f : β₁ → β₂) (g : α → β₂ → α) (l : Vector β₁ n) (init : α) :
    (l.map f).foldl g init = l.foldl (fun x y => g x (f y)) init := by
  cases l; simp [Array.foldl_map']

theorem foldr_map (f : α₁ → α₂) (g : α₂ → β → β) (l : Vector α₁ n) (init : β) :
    (l.map f).foldr g init = l.foldr (fun x y => g (f x) y) init := by
  cases l; simp [Array.foldr_map']

theorem foldl_filterMap (f : α → Option β) (g : γ → β → γ) (l : Vector α n) (init : γ) :
    (l.filterMap f).foldl g init = l.foldl (fun x y => match f y with | some b => g x b | none => x) init := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldl_filterMap']
  rfl

theorem foldr_filterMap (f : α → Option β) (g : β → γ → γ) (l : Vector α n) (init : γ) :
    (l.filterMap f).foldr g init = l.foldr (fun x y => match f x with | some b => g b y | none => y) init := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldr_filterMap']
  rfl

theorem foldl_map_hom (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : Vector α n)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (l.map g).foldl f' (g a) = g (l.foldl f a) := by
  rcases l with ⟨l, rfl⟩
  simp
  rw [Array.foldl_map_hom' _ _ _ _ _ h rfl]

theorem foldr_map_hom (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : Vector α n)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (l.map g).foldr f' (g a) = g (l.foldr f a) := by
  rcases l with ⟨l, rfl⟩
  simp
  rw [Array.foldr_map_hom' _ _ _ _ _ h rfl]

@[simp] theorem foldrM_append [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (l : Vector α n) (l' : Vector α k) :
    (l ++ l').foldrM f b = l'.foldrM f b >>= l.foldrM f := by
  rcases l with ⟨l, rfl⟩
  rcases l' with ⟨l', rfl⟩
  simp

@[simp] theorem foldl_append {β : Type _} (f : β → α → β) (b) (l : Vector α n) (l' : Vector α k) :
    (l ++ l').foldl f b = l'.foldl f (l.foldl f b) := by simp [foldl_eq_foldlM]

@[simp] theorem foldr_append (f : α → β → β) (b) (l : Vector α n) (l' : Vector α k) :
    (l ++ l').foldr f b = l.foldr f (l'.foldr f b) := by simp [foldr_eq_foldrM]

@[simp] theorem foldl_flatten (f : β → α → β) (b : β) (L : Vector (Vector α m) n) :
    (flatten L).foldl f b = L.foldl (fun b l => l.foldl f b) b := by
  cases L using vector₂_induction
  simp [Array.foldl_flatten', Array.foldl_map']

@[simp] theorem foldr_flatten (f : α → β → β) (b : β) (L : Vector (Vector α m) n) :
    (flatten L).foldr f b = L.foldr (fun l b => l.foldr f b) b := by
  cases L using vector₂_induction
  simp [Array.foldr_flatten', Array.foldr_map']

@[simp] theorem foldl_reverse (l : Vector α n) (f : β → α → β) (b) :
    l.reverse.foldl f b = l.foldr (fun x y => f y x) b := by simp [foldl_eq_foldlM, foldr_eq_foldrM]

@[simp] theorem foldr_reverse (l : Vector α n) (f : α → β → β) (b) :
    l.reverse.foldr f b = l.foldl (fun x y => f y x) b :=
  (foldl_reverse ..).symm.trans <| by simp

theorem foldl_eq_foldr_reverse (l : Vector α n) (f : β → α → β) (b) :
    l.foldl f b = l.reverse.foldr (fun x y => f y x) b := by simp

theorem foldr_eq_foldl_reverse (l : Vector α n) (f : α → β → β) (b) :
    l.foldr f b = l.reverse.foldl (fun x y => f y x) b := by simp

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op] {l : Vector α n} {a₁ a₂} :
     l.foldl op (op a₁ a₂) = op a₁ (l.foldl op a₂) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldl_assoc]

@[simp] theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op] {l : Vector α n} {a₁ a₂} :
    l.foldr op (op a₁ a₂) = op (l.foldr op a₁) a₂ := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldr_assoc]

theorem foldl_hom (f : α₁ → α₂) (g₁ : α₁ → β → α₁) (g₂ : α₂ → β → α₂) (l : Vector β n) (init : α₁)
    (H : ∀ x y, g₂ (f x) y = f (g₁ x y)) : l.foldl g₂ (f init) = f (l.foldl g₁ init) := by
  rcases l with ⟨l, rfl⟩
  simp
  rw [Array.foldl_hom _ _ _ _ _ H]

theorem foldr_hom (f : β₁ → β₂) (g₁ : α → β₁ → β₁) (g₂ : α → β₂ → β₂) (l : Vector α n) (init : β₁)
    (H : ∀ x y, g₂ x (f y) = f (g₁ x y)) : l.foldr g₂ (f init) = f (l.foldr g₁ init) := by
  cases l
  simp
  rw [Array.foldr_hom _ _ _ _ _ H]

/--
We can prove that two folds over the same array are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the array,
preserves the relation.
-/
theorem foldl_rel {l : Array α} {f g : β → α → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ l → ∀ (c c' : β), r c c' → r (f c a) (g c' a)) :
    r (l.foldl (fun acc a => f acc a) a) (l.foldl (fun acc a => g acc a) b) := by
  rcases l with ⟨l⟩
  simpa using List.foldl_rel r h (by simpa using h')

/--
We can prove that two folds over the same array are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the array,
preserves the relation.
-/
theorem foldr_rel {l : Array α} {f g : α → β → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ l → ∀ (c c' : β), r c c' → r (f a c) (g a c')) :
    r (l.foldr (fun a acc => f a acc) a) (l.foldr (fun a acc => g a acc) b) := by
  rcases l with ⟨l⟩
  simpa using List.foldr_rel r h (by simpa using h')

@[simp] theorem foldl_add_const (l : Array α) (a b : Nat) :
    l.foldl (fun x _ => x + a) b = b + a * l.size := by
  rcases l with ⟨l⟩
  simp

@[simp] theorem foldr_add_const (l : Array α) (a b : Nat) :
    l.foldr (fun _ x => x + a) b = b + a * l.size := by
  rcases l with ⟨l⟩
  simp


/-! Content below this point has not yet been aligned with `List` and `Array`. -/

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
    simp [back]

/-! ### zipWith -/

@[simp] theorem getElem_zipWith (f : α → β → γ) (a : Vector α n) (b : Vector β n) (i : Nat)
    (hi : i < n) : (zipWith f a b)[i] = f a[i] b[i] := by
  cases a
  cases b
  simp

/-! ### take -/

@[simp] theorem take_size (a : Vector α n) : a.take n = a.cast (by simp) := by
  rcases a with ⟨a, rfl⟩
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
