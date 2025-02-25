/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Francois Dorais, Kim Morrison
-/
prelude
import Init.Data.Vector.Basic
import Init.Data.Array.Attach
import Init.Data.Array.Find

/-!
## Vectors
Lemmas about `Vector α n`
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

theorem toVector_inj {xs ys : Array α} (h₁ : xs.size = ys.size) (h₂ : xs.toVector.cast h₁ = ys.toVector) : xs = ys := by
  ext i ih₁ ih₂
  · exact h₁
  · simpa using congrArg (fun xs => xs[i]) h₂

end Array

namespace Vector

/-! ### mk lemmas -/

theorem toArray_mk (xs : Array α) (h : xs.size = n) : (Vector.mk xs h).toArray = xs := rfl

@[simp] theorem mk_toArray (xs : Vector α n) : mk xs.toArray xs.2 = xs := by
  rfl

@[simp] theorem getElem_mk {xs : Array α} {size : xs.size = n} {i : Nat} (h : i < n) :
    (Vector.mk xs size)[i] = xs[i] := rfl

@[simp] theorem getElem?_mk {xs : Array α} {size : xs.size = n} {i : Nat} :
    (Vector.mk xs size)[i]? = xs[i]? := by
  subst size
  simp [getElem?_def]

@[simp] theorem mem_mk {xs : Array α} {size : xs.size = n} {a : α} :
    a ∈ Vector.mk xs size ↔ a ∈ xs :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp] theorem contains_mk [BEq α] {xs : Array α} {size : xs.size = n} {a : α} :
    (Vector.mk xs size).contains a = xs.contains a := by
  simp [contains]

@[simp] theorem push_mk {xs : Array α} {size : xs.size = n} {x : α} :
    (Vector.mk xs size).push x =
      Vector.mk (xs.push x) (by simp [size, Nat.succ_eq_add_one]) := rfl

@[simp] theorem pop_mk {xs : Array α} {size : xs.size = n} :
    (Vector.mk xs size).pop = Vector.mk xs.pop (by simp [size]) := rfl

@[simp] theorem mk_beq_mk [BEq α] {xs ys : Array α} {h : xs.size = n} {h' : ys.size = n} :
    (Vector.mk xs h == Vector.mk ys h') = (xs == ys) := by
  simp [instBEq, isEqv, Array.instBEq, Array.isEqv, h, h']

@[simp] theorem allDiff_mk [BEq α] (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).allDiff = xs.allDiff := rfl

@[simp] theorem mk_append_mk (xs ys : Array α) (h : xs.size = n) (h' : ys.size = m) :
    Vector.mk xs h ++ Vector.mk ys h' = Vector.mk (xs ++ ys) (by simp [h, h']) := rfl

@[simp] theorem back!_mk [Inhabited α] (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).back! = xs.back! := rfl

@[simp] theorem back?_mk (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).back? = xs.back? := rfl

@[simp] theorem back_mk [NeZero n] (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).back = xs.back (by have : 0 ≠ n := NeZero.ne' n; omega) := by
  simp [back, Array.back, h]

@[simp] theorem foldlM_mk [Monad m] (f : β → α → m β) (b : β) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).foldlM f b = xs.foldlM f b := rfl

@[simp] theorem foldrM_mk [Monad m] (f : α → β → m β) (b : β) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).foldrM f b = xs.foldrM f b := rfl

@[simp] theorem foldl_mk (f : β → α → β) (b : β) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).foldl f b = xs.foldl f b := rfl

@[simp] theorem foldr_mk (f : α → β → β) (b : β) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).foldr f b = xs.foldr f b := rfl

@[simp] theorem drop_mk (xs : Array α) (h : xs.size = n) (i) :
    (Vector.mk xs h).drop i = Vector.mk (xs.extract i xs.size) (by simp [h]) := rfl

@[simp] theorem eraseIdx_mk (xs : Array α) (h : xs.size = n) (i) (h') :
    (Vector.mk xs h).eraseIdx i h' = Vector.mk (xs.eraseIdx i) (by simp [h]) := rfl

@[simp] theorem eraseIdx!_mk (xs : Array α) (h : xs.size = n) (i) (hi : i < n) :
    (Vector.mk xs h).eraseIdx! i = Vector.mk (xs.eraseIdx i) (by simp [h, hi]) := by
  simp [Vector.eraseIdx!, hi]

@[simp] theorem insertIdx_mk (xs : Array α) (h : xs.size = n) (i x) (h') :
    (Vector.mk xs h).insertIdx i x h' = Vector.mk (xs.insertIdx i x) (by simp [h, h']) := rfl

@[simp] theorem insertIdx!_mk (xs : Array α) (h : xs.size = n) (i x) (hi : i ≤ n) :
    (Vector.mk xs h).insertIdx! i x = Vector.mk (xs.insertIdx i x) (by simp [h, hi]) := by
  simp [Vector.insertIdx!, hi]

@[simp] theorem cast_mk (xs : Array α) (h : xs.size = n) (h' : n = m) :
    (Vector.mk xs h).cast h' = Vector.mk xs (by simp [h, h']) := rfl

@[simp] theorem extract_mk (xs : Array α) (h : xs.size = n) (start stop) :
    (Vector.mk xs h).extract start stop = Vector.mk (xs.extract start stop) (by simp [h]) := rfl

@[simp] theorem finIdxOf?_mk [BEq α] (xs : Array α) (h : xs.size = n) (x : α) :
    (Vector.mk xs h).finIdxOf? x = (xs.finIdxOf? x).map (Fin.cast h) := rfl

@[simp] theorem findFinIdx?_mk (xs : Array α) (h : xs.size = n) (f : α → Bool) :
    (Vector.mk xs h).findFinIdx? f = (xs.findFinIdx? f).map (Fin.cast h) := rfl

@[deprecated finIdxOf?_mk (since := "2025-01-29")]
abbrev indexOf?_mk := @finIdxOf?_mk

@[simp] theorem findM?_mk [Monad m] (xs : Array α) (h : xs.size = n) (f : α → m Bool) :
    (Vector.mk xs h).findM? f = xs.findM? f := rfl

@[simp] theorem findSomeM?_mk [Monad m] (xs : Array α) (h : xs.size = n) (f : α → m (Option β)) :
    (Vector.mk xs h).findSomeM? f = xs.findSomeM? f := rfl

@[simp] theorem findRevM?_mk [Monad m] (xs : Array α) (h : xs.size = n) (f : α → m Bool) :
    (Vector.mk xs h).findRevM? f = xs.findRevM? f := rfl

@[simp] theorem findSomeRevM?_mk [Monad m] (xs : Array α) (h : xs.size = n) (f : α → m (Option β)) :
    (Vector.mk xs h).findSomeRevM? f = xs.findSomeRevM? f := rfl

@[simp] theorem find?_mk (xs : Array α) (h : xs.size = n) (f : α → Bool) :
    (Vector.mk xs h).find? f = xs.find? f := rfl

@[simp] theorem findSome?_mk (xs : Array α) (h : xs.size = n) (f : α → Option β) :
    (Vector.mk xs h).findSome? f = xs.findSome? f := rfl

@[simp] theorem findRev?_mk (xs : Array α) (h : xs.size = n) (f : α → Bool) :
    (Vector.mk xs h).findRev? f = xs.findRev? f := rfl

@[simp] theorem findSomeRev?_mk (xs : Array α) (h : xs.size = n) (f : α → Option β) :
    (Vector.mk xs h).findSomeRev? f = xs.findSomeRev? f := rfl

@[simp] theorem mk_isEqv_mk (r : α → α → Bool) (xs ys : Array α) (h : xs.size = n) (h' : ys.size = n) :
    Vector.isEqv (Vector.mk xs h) (Vector.mk ys h') r = Array.isEqv xs ys r := by
  simp [Vector.isEqv, Array.isEqv, h, h']

@[simp] theorem mk_isPrefixOf_mk [BEq α] (xs ys : Array α) (h : xs.size = n) (h' : ys.size = n) :
    (Vector.mk xs h).isPrefixOf (Vector.mk ys h') = xs.isPrefixOf ys := by
  simp [Vector.isPrefixOf, Array.isPrefixOf, h, h']

@[simp] theorem map_mk (xs : Array α) (h : xs.size = n) (f : α → β) :
    (Vector.mk xs h).map f = Vector.mk (xs.map f) (by simp [h]) := rfl

@[simp] theorem mapIdx_mk (xs : Array α) (h : xs.size = n) (f : Nat → α → β) :
    (Vector.mk xs h).mapIdx f = Vector.mk (xs.mapIdx f) (by simp [h]) := rfl

@[simp] theorem mapFinIdx_mk (xs : Array α) (h : xs.size = n) (f : (i : Nat) → α → (h : i < n) → β) :
    (Vector.mk xs h).mapFinIdx f =
      Vector.mk (xs.mapFinIdx fun i a h' => f i a (by simpa [h] using h')) (by simp [h]) := rfl

@[simp] theorem forM_mk [Monad m] (f : α → m PUnit) (xs : Array α) (h : xs.size = n) :
    forM (Vector.mk xs h) f = forM xs f := rfl

@[simp] theorem forIn'_mk [Monad m]
    (xs : Array α) (h : xs.size = n) (b : β)
    (f : (a : α) → a ∈ Vector.mk xs h → β → m (ForInStep β)) :
    forIn' (Vector.mk xs h) b f = forIn' xs b (fun a m b => f a (by simpa using m) b) := rfl

@[simp] theorem forIn_mk [Monad m]
    (xs : Array α) (h : xs.size = n) (b : β) (f : (a : α) → β → m (ForInStep β)) :
    forIn (Vector.mk xs h) b f = forIn xs b f := rfl

@[simp] theorem flatMap_mk (f : α → Vector β m) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).flatMap f =
      Vector.mk (xs.flatMap (fun a => (f a).toArray)) (by simp [h, Array.map_const']) := rfl

@[simp] theorem firstM_mk [Alternative m] (f : α → m β) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).firstM f = xs.firstM f := rfl

@[simp] theorem reverse_mk (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).reverse = Vector.mk xs.reverse (by simp [h]) := rfl

@[simp] theorem set_mk (xs : Array α) (h : xs.size = n) (i x w) :
    (Vector.mk xs h).set i x = Vector.mk (xs.set i x) (by simp [h]) := rfl

@[simp] theorem set!_mk (xs : Array α) (h : xs.size = n) (i x) :
    (Vector.mk xs h).set! i x = Vector.mk (xs.set! i x) (by simp [h]) := rfl

@[simp] theorem setIfInBounds_mk (xs : Array α) (h : xs.size = n) (i x) :
    (Vector.mk xs h).setIfInBounds i x = Vector.mk (xs.setIfInBounds i x) (by simp [h]) := rfl

@[simp] theorem swap_mk (xs : Array α) (h : xs.size = n) (i j) (hi hj) :
    (Vector.mk xs h).swap i j = Vector.mk (xs.swap i j) (by simp [h]) :=
  rfl

@[simp] theorem swapIfInBounds_mk (xs : Array α) (h : xs.size = n) (i j) :
    (Vector.mk xs h).swapIfInBounds i j = Vector.mk (xs.swapIfInBounds i j) (by simp [h]) := rfl

@[simp] theorem swapAt_mk (xs : Array α) (h : xs.size = n) (i x) (hi) :
    (Vector.mk xs h).swapAt i x =
      ((xs.swapAt i x).fst, Vector.mk (xs.swapAt i x).snd (by simp [h])) :=
  rfl

@[simp] theorem swapAt!_mk (xs : Array α) (h : xs.size = n) (i x) : (Vector.mk xs h).swapAt! i x =
    ((xs.swapAt! i x).fst, Vector.mk (xs.swapAt! i x).snd (by simp [h])) := rfl

@[simp] theorem take_mk (xs : Array α) (h : xs.size = n) (i) :
    (Vector.mk xs h).take i = Vector.mk (xs.take i) (by simp [h]) := rfl

@[simp] theorem zipIdx_mk (xs : Array α) (h : xs.size = n) (k : Nat := 0) :
    (Vector.mk xs h).zipIdx k = Vector.mk (xs.zipIdx k) (by simp [h]) := rfl

@[deprecated zipIdx_mk (since := "2025-01-21")]
abbrev zipWithIndex_mk := @zipIdx_mk

@[simp] theorem mk_zipWith_mk (f : α → β → γ) (as : Array α) (bs : Array β)
      (h : as.size = n) (h' : bs.size = n) : zipWith f (Vector.mk as h) (Vector.mk bs h') =
        Vector.mk (Array.zipWith f as bs) (by simp [h, h']) := rfl

@[simp] theorem mk_zip_mk (as : Array α) (bs : Array β) (h : as.size = n) (h' : bs.size = n) :
    zip (Vector.mk as h) (Vector.mk bs h') = Vector.mk (Array.zip as bs) (by simp [h, h']) := rfl

@[simp] theorem unzip_mk (xs : Array (α × β)) (h : xs.size = n) :
    (Vector.mk xs h).unzip = (Vector.mk xs.unzip.1 (by simp_all), Vector.mk xs.unzip.2 (by simp_all)) := rfl

@[simp] theorem anyM_mk [Monad m] (p : α → m Bool) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).anyM p = xs.anyM p := rfl

@[simp] theorem allM_mk [Monad m] (p : α → m Bool) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).allM p = xs.allM p := rfl

@[simp] theorem any_mk (p : α → Bool) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).any p = xs.any p := rfl

@[simp] theorem all_mk (p : α → Bool) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).all p = xs.all p := rfl

@[simp] theorem countP_mk (p : α → Bool) (xs : Array α) (h : xs.size = n) :
    (Vector.mk xs h).countP p = xs.countP p := rfl

@[simp] theorem count_mk [BEq α] (xs : Array α) (h : xs.size = n) (a : α) :
    (Vector.mk xs h).count a = xs.count a := rfl

@[simp] theorem eq_mk : xs = Vector.mk as h ↔ xs.toArray = as := by
  cases xs
  simp

@[simp] theorem mk_eq : Vector.mk as h = xs ↔ as = xs.toArray := by
  cases xs
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

@[simp] theorem toArray_append (xs : Vector α m) (ys : Vector α n) :
    (xs ++ ys).toArray = xs.toArray ++ ys.toArray := rfl

@[simp] theorem toArray_drop (xs : Vector α n) (i) :
    (xs.drop i).toArray = xs.toArray.extract i xs.size := rfl

@[simp] theorem toArray_empty : (#v[] : Vector α 0).toArray = #[] := rfl

@[simp] theorem toArray_mkEmpty (cap) :
    (Vector.mkEmpty (α := α) cap).toArray = Array.mkEmpty cap := rfl

@[simp] theorem toArray_eraseIdx (xs : Vector α n) (i) (h) :
    (xs.eraseIdx i h).toArray = xs.toArray.eraseIdx i (by simp [h]) := rfl

@[simp] theorem toArray_eraseIdx! (xs : Vector α n) (i) (hi : i < n) :
    (xs.eraseIdx! i).toArray = xs.toArray.eraseIdx! i := by
  cases xs; simp_all [Array.eraseIdx!]

@[simp] theorem toArray_insertIdx (xs : Vector α n) (i x) (h) :
    (xs.insertIdx i x h).toArray = xs.toArray.insertIdx i x (by simp [h]) := rfl

@[simp] theorem toArray_insertIdx! (xs : Vector α n) (i x) (hi : i ≤ n) :
    (xs.insertIdx! i x).toArray = xs.toArray.insertIdx! i x := by
  cases xs; simp_all [Array.insertIdx!]

@[simp] theorem toArray_cast (xs : Vector α n) (h : n = m) :
    (xs.cast h).toArray = xs.toArray := rfl

@[simp] theorem toArray_extract (xs : Vector α n) (start stop) :
    (xs.extract start stop).toArray = xs.toArray.extract start stop := rfl

@[simp] theorem toArray_map (f : α → β) (xs : Vector α n) :
    (xs.map f).toArray = xs.toArray.map f := rfl

@[simp] theorem toArray_mapIdx (f : Nat → α → β) (xs : Vector α n) :
    (xs.mapIdx f).toArray = xs.toArray.mapIdx f := rfl

@[simp] theorem toArray_mapFinIdx (f : (i : Nat) → α → (h : i < n) → β) (xs : Vector α n) :
    (xs.mapFinIdx f).toArray =
      xs.toArray.mapFinIdx (fun i a h => f i a (by simpa [xs.size_toArray] using h)) :=
  rfl

theorem toArray_mapM_go [Monad m] [LawfulMonad m] (f : α → m β) (xs : Vector α n) (i h acc) :
    toArray <$> mapM.go f xs i h acc = Array.mapM.map f xs.toArray i acc.toArray := by
  unfold mapM.go
  unfold Array.mapM.map
  simp only [xs.size_toArray, getElem_toArray]
  split
  · simp only [map_bind]
    congr
    funext b
    rw [toArray_mapM_go]
    rfl
  · simp

@[simp] theorem toArray_mapM [Monad m] [LawfulMonad m] (f : α → m β) (xs : Vector α n) :
    toArray <$> xs.mapM f = xs.toArray.mapM f := by
  rcases xs with ⟨xs, rfl⟩
  unfold mapM
  rw [toArray_mapM_go]
  rfl

@[simp] theorem toArray_ofFn (f : Fin n → α) : (Vector.ofFn f).toArray = Array.ofFn f := rfl

@[simp] theorem toArray_pop (xs : Vector α n) : xs.pop.toArray = xs.toArray.pop := rfl

@[simp] theorem toArray_push (xs : Vector α n) (x) : (xs.push x).toArray = xs.toArray.push x := rfl

@[simp] theorem toArray_beq_toArray [BEq α] (xs : Vector α n) (ys : Vector α n) :
    (xs.toArray == ys.toArray) = (xs == ys) := by
  simp [instBEq, isEqv, Array.instBEq, Array.isEqv, xs.2, ys.2]

@[simp] theorem toArray_range : (Vector.range n).toArray = Array.range n := rfl

@[simp] theorem toArray_reverse (xs : Vector α n) : xs.reverse.toArray = xs.toArray.reverse := rfl

@[simp] theorem toArray_set (xs : Vector α n) (i x h) :
    (xs.set i x).toArray = xs.toArray.set i x (by simpa using h):= rfl

@[simp] theorem toArray_set! (xs : Vector α n) (i x) :
    (xs.set! i x).toArray = xs.toArray.set! i x := rfl

@[simp] theorem toArray_setIfInBounds (xs : Vector α n) (i x) :
    (xs.setIfInBounds i x).toArray = xs.toArray.setIfInBounds i x := rfl

@[simp] theorem toArray_singleton (x : α) : (Vector.singleton x).toArray = #[x] := rfl

@[simp] theorem toArray_swap (xs : Vector α n) (i j) (hi hj) : (xs.swap i j).toArray =
    xs.toArray.swap i j (by simp [hi, hj]) (by simp [hi, hj]) := rfl

@[simp] theorem toArray_swapIfInBounds (xs : Vector α n) (i j) :
    (xs.swapIfInBounds i j).toArray = xs.toArray.swapIfInBounds i j := rfl

@[simp] theorem toArray_swapAt (xs : Vector α n) (i x h) :
    ((xs.swapAt i x).fst, (xs.swapAt i x).snd.toArray) =
      ((xs.toArray.swapAt i x (by simpa using h)).fst,
        (xs.toArray.swapAt i x (by simpa using h)).snd) := rfl

@[simp] theorem toArray_swapAt! (xs : Vector α n) (i x) :
    ((xs.swapAt! i x).fst, (xs.swapAt! i x).snd.toArray) =
      ((xs.toArray.swapAt! i x).fst, (xs.toArray.swapAt! i x).snd) := rfl

@[simp] theorem toArray_take (xs : Vector α n) (i) : (xs.take i).toArray = xs.toArray.take i := rfl

@[simp] theorem toArray_zipIdx (xs : Vector α n) (k : Nat := 0) :
    (xs.zipIdx k).toArray = xs.toArray.zipIdx k := rfl

@[simp] theorem toArray_zipWith (f : α → β → γ) (as : Vector α n) (bs : Vector β n) :
    (Vector.zipWith f as bs).toArray = Array.zipWith f as.toArray bs.toArray := rfl

@[simp] theorem anyM_toArray [Monad m] (p : α → m Bool) (xs : Vector α n) :
    xs.toArray.anyM p = xs.anyM p := by
  cases xs
  simp

@[simp] theorem allM_toArray [Monad m] (p : α → m Bool) (xs : Vector α n) :
    xs.toArray.allM p = xs.allM p := by
  cases xs
  simp

@[simp] theorem any_toArray (p : α → Bool) (xs : Vector α n) :
    xs.toArray.any p = xs.any p := by
  cases xs
  simp

@[simp] theorem all_toArray (p : α → Bool) (xs : Vector α n) :
    xs.toArray.all p = xs.all p := by
  cases xs
  simp

@[simp] theorem countP_toArray (p : α → Bool) (xs : Vector α n) :
    xs.toArray.countP p = xs.countP p := by
  cases xs
  simp

@[simp] theorem count_toArray [BEq α] (a : α) (xs : Vector α n) :
    xs.toArray.count a = xs.count a := by
  cases xs
  simp

@[simp] theorem find?_toArray (p : α → Bool) (xs : Vector α n) :
    xs.toArray.find? p = xs.find? p := by
  cases xs
  simp

@[simp] theorem findSome?_toArray (f : α → Option β) (xs : Vector α n) :
    xs.toArray.findSome? f = xs.findSome? f := by
  cases xs
  simp

@[simp] theorem findRev?_toArray (p : α → Bool) (xs : Vector α n) :
    xs.toArray.findRev? p = xs.findRev? p := by
  cases xs
  simp

@[simp] theorem findSomeRev?_toArray (f : α → Option β) (xs : Vector α n) :
    xs.toArray.findSomeRev? f = xs.findSomeRev? f := by
  cases xs
  simp

@[simp] theorem findM?_toArray [Monad m] (p : α → m Bool) (xs : Vector α n) :
    xs.toArray.findM? p = xs.findM? p := by
  cases xs
  simp

@[simp] theorem findSomeM?_toArray [Monad m] (f : α → m (Option β)) (xs : Vector α n) :
    xs.toArray.findSomeM? f = xs.findSomeM? f := by
  cases xs
  simp

@[simp] theorem findRevM?_toArray [Monad m] (p : α → m Bool) (xs : Vector α n) :
    xs.toArray.findRevM? p = xs.findRevM? p := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem findSomeRevM?_toArray [Monad m] (f : α → m (Option β)) (xs : Vector α n) :
    xs.toArray.findSomeRevM? f = xs.findSomeRevM? f := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem finIdxOf?_toArray [BEq α] (a : α) (xs : Vector α n) :
    xs.toArray.finIdxOf? a = (xs.finIdxOf? a).map (Fin.cast xs.size_toArray.symm) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem findFinIdx?_toArray (p : α → Bool) (xs : Vector α n) :
    xs.toArray.findFinIdx? p = (xs.findFinIdx? p).map (Fin.cast xs.size_toArray.symm) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem toArray_mkVector : (mkVector n a).toArray = mkArray n a := rfl

@[simp] theorem toArray_inj {xs ys : Vector α n} : xs.toArray = ys.toArray ↔ xs = ys := by
  cases xs
  cases ys
  simp

/--
`Vector.ext` is an extensionality theorem.
Vectors `a` and `b` are equal to each other if their elements are equal for each valid index.
-/
@[ext]
protected theorem ext {xs ys : Vector α n} (h : (i : Nat) → (_ : i < n) → xs[i] = ys[i]) : xs = ys := by
  apply Vector.toArray_inj.1
  apply Array.ext
  · rw [xs.size_toArray, ys.size_toArray]
  · intro i hi _
    rw [xs.size_toArray] at hi
    exact h i hi

@[simp] theorem toArray_eq_empty_iff (xs : Vector α n) : xs.toArray = #[] ↔ n = 0 := by
  rcases xs with ⟨xs, h⟩
  exact ⟨by rintro rfl; simp_all, by rintro rfl; simpa using h⟩

/-! ### toList -/

theorem toArray_toList (xs : Vector α n) : xs.toArray.toList = xs.toList := rfl

@[simp] theorem getElem_toList {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toList.length) :
    xs.toList[i] = xs[i]'(by simpa using h) := by
  cases xs
  simp

@[simp] theorem getElem?_toList {α n} (xs : Vector α n) (i : Nat) :
    xs.toList[i]? = xs[i]? := by
  cases xs
  simp

theorem toList_append (xs : Vector α m) (ys : Vector α n) :
    (xs ++ ys).toList = xs.toList ++ ys.toList := by simp

@[simp] theorem toList_drop (xs : Vector α n) (i) :
    (xs.drop i).toList = xs.toList.drop i := by
  simp [List.take_of_length_le]

theorem toList_empty : (#v[] : Vector α 0).toArray = #[] := by simp

theorem toList_mkEmpty (cap) :
    (Vector.mkEmpty (α := α) cap).toList = [] := rfl

theorem toList_eraseIdx (xs : Vector α n) (i) (h) :
    (xs.eraseIdx i h).toList = xs.toList.eraseIdx i := by simp

@[simp] theorem toList_eraseIdx! (xs : Vector α n) (i) (hi : i < n) :
    (xs.eraseIdx! i).toList = xs.toList.eraseIdx i := by
  cases xs; simp_all [Array.eraseIdx!]

theorem toList_insertIdx (xs : Vector α n) (i x) (h) :
    (xs.insertIdx i x h).toList = xs.toList.insertIdx i x := by simp

theorem toList_insertIdx! (xs : Vector α n) (i x) (hi : i ≤ n) :
    (xs.insertIdx! i x).toList = xs.toList.insertIdx i x := by
  cases xs; simp_all [Array.insertIdx!]

theorem toList_cast (xs : Vector α n) (h : n = m) :
    (xs.cast h).toList = xs.toList := rfl

theorem toList_extract (xs : Vector α n) (start stop) :
    (xs.extract start stop).toList = (xs.toList.drop start).take (stop - start) := by
  simp

theorem toList_map (f : α → β) (xs : Vector α n) :
    (xs.map f).toList = xs.toList.map f := by simp

theorem toList_mapIdx (f : Nat → α → β) (xs : Vector α n) :
    (xs.mapIdx f).toList = xs.toList.mapIdx f := by simp

theorem toList_mapFinIdx (f : (i : Nat) → α → (h : i < n) → β) (xs : Vector α n) :
    (xs.mapFinIdx f).toList =
      xs.toList.mapFinIdx (fun i a h => f i a (by simpa [xs.size_toArray] using h)) := by
  simp

theorem toList_ofFn (f : Fin n → α) : (Vector.ofFn f).toList = List.ofFn f := by simp

theorem toList_pop (xs : Vector α n) : xs.pop.toList = xs.toList.dropLast := rfl

theorem toList_push (xs : Vector α n) (x) : (xs.push x).toList = xs.toList ++ [x] := by simp

@[simp] theorem toList_beq_toList [BEq α] (xs : Vector α n) (ys : Vector α n) :
    (xs.toList == ys.toList) = (xs == ys) := by
  simp [instBEq, isEqv, Array.instBEq, Array.isEqv, xs.2, ys.2]

theorem toList_range : (Vector.range n).toList = List.range n := by simp

theorem toList_reverse (xs : Vector α n) : xs.reverse.toList = xs.toList.reverse := by simp

theorem toList_set (xs : Vector α n) (i x h) :
    (xs.set i x).toList = xs.toList.set i x := rfl

@[simp] theorem toList_setIfInBounds (xs : Vector α n) (i x) :
    (xs.setIfInBounds i x).toList = xs.toList.set i x := by
  simp [Vector.setIfInBounds]

theorem toList_singleton (x : α) : (Vector.singleton x).toList = [x] := rfl

theorem toList_swap (xs : Vector α n) (i j) (hi hj) :
    (xs.swap i j).toList = (xs.toList.set i xs[j]).set j xs[i] := rfl

@[simp] theorem toList_take (xs : Vector α n) (i) : (xs.take i).toList = xs.toList.take i := by
  simp [List.take_of_length_le]

@[simp] theorem toList_zipWith (f : α → β → γ) (as : Vector α n) (bs : Vector β n) :
    (Vector.zipWith f as bs).toArray = Array.zipWith f as.toArray bs.toArray := rfl

@[simp] theorem anyM_toList [Monad m] (p : α → m Bool) (xs : Vector α n) :
    xs.toList.anyM p = xs.anyM p := by
  cases xs
  simp

@[simp] theorem allM_toList [Monad m] [LawfulMonad m] (p : α → m Bool) (xs : Vector α n) :
    xs.toList.allM p = xs.allM p := by
  cases xs
  simp

@[simp] theorem any_toList (p : α → Bool) (xs : Vector α n) :
    xs.toList.any p = xs.any p := by
  cases xs
  simp

@[simp] theorem all_toList (p : α → Bool) (xs : Vector α n) :
    xs.toList.all p = xs.all p := by
  cases xs
  simp

@[simp] theorem countP_toList (p : α → Bool) (xs : Vector α n) :
    xs.toList.countP p = xs.countP p := by
  cases xs
  simp

@[simp] theorem count_toList [BEq α] (a : α) (xs : Vector α n) :
    xs.toList.count a = xs.count a := by
  cases xs
  simp

@[simp] theorem find?_toList (p : α → Bool) (xs : Vector α n) :
    xs.toList.find? p = xs.find? p := by
  cases xs
  simp

@[simp] theorem findSome?_toList (f : α → Option β) (xs : Vector α n) :
    xs.toList.findSome? f = xs.findSome? f := by
  cases xs
  simp

@[simp] theorem findM?_toList [Monad m] [LawfulMonad m] (p : α → m Bool) (xs : Vector α n) :
    xs.toList.findM? p = xs.findM? p := by
  cases xs
  simp

@[simp] theorem findSomeM?_toList [Monad m] [LawfulMonad m] (f : α → m (Option β)) (xs : Vector α n) :
    xs.toList.findSomeM? f = xs.findSomeM? f := by
  cases xs
  simp

@[simp] theorem finIdxOf?_toList [BEq α] (a : α) (xs : Vector α n) :
    xs.toList.finIdxOf? a = (xs.finIdxOf? a).map (Fin.cast xs.size_toArray.symm) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem findFinIdx?_toList (p : α → Bool) (xs : Vector α n) :
    xs.toList.findFinIdx? p = (xs.findFinIdx? p).map (Fin.cast xs.size_toArray.symm) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem toList_mkVector : (mkVector n a).toList = List.replicate n a := rfl

theorem toList_inj {xs ys : Vector α n} : xs.toList = ys.toList ↔ xs = ys := by
  cases xs
  cases ys
  simp [Array.toList_inj]

@[simp] theorem toList_eq_empty_iff (xs : Vector α n) : xs.toList = [] ↔ n = 0 := by
  rcases xs with ⟨xs, h⟩
  simp only [Array.toList_eq_nil_iff]
  exact ⟨by rintro rfl; simp_all, by rintro rfl; simpa using h⟩

@[simp] theorem mem_toList_iff (a : α) (xs : Vector α n) : a ∈ xs.toList ↔ a ∈ xs := by
  simp

theorem length_toList {α n} (xs : Vector α n) : xs.toList.length = n := by simp

/-! ### empty -/

@[simp] theorem empty_eq {xs : Vector α 0} : #v[] = xs ↔ xs = #v[] := by
  cases xs
  simp

/-- A vector of length `0` is the empty vector. -/
protected theorem eq_empty (xs : Vector α 0) : xs = #v[] := by
  apply Vector.toArray_inj.1
  apply Array.eq_empty_of_size_eq_zero xs.2


/-! ### size -/

theorem eq_empty_of_size_eq_zero (xs : Vector α n) (h : n = 0) : xs = #v[].cast h.symm := by
  rcases xs with ⟨xs, rfl⟩
  apply toArray_inj.1
  simp only [List.length_eq_zero_iff, Array.toList_eq_nil_iff] at h
  simp [h]

theorem size_eq_one {xs : Vector α 1} : ∃ a, xs = #v[a] := by
  rcases xs with ⟨xs, h⟩
  simpa using Array.size_eq_one_iff.mp h

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

@[simp] theorem getElem_cast (xs : Vector α n) (h : n = m) (i : Nat) (hi : i < m) :
    (xs.cast h)[i] = xs[i] := by
  cases xs
  simp

@[simp] theorem getElem?_cast {xs : Vector α n} {m : Nat} {w : n = m} {i : Nat} :
    (xs.cast w)[i]? = xs[i]? := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem mem_cast {a : α} {xs : Vector α n} {m : Nat} {w : n = m} :
    a ∈ xs.cast w ↔ a ∈ xs := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem cast_cast {xs : Vector α n} {w : n = m} {w' : m = k} :
    (xs.cast w).cast w' = xs.cast (w.trans w') := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem cast_rfl {xs : Vector α n} : xs.cast rfl = xs := by
  rcases xs with ⟨xs, rfl⟩
  simp

/-- In an equality between two casts, push the casts to the right hand side. -/
@[simp] theorem cast_eq_cast {as : Vector α n} {bs : Vector α m} {wa : n = k} {wb : m = k} :
    as.cast wa = bs.cast wb ↔ as = bs.cast (by omega) := by
  constructor
  · intro w
    ext i h
    replace w := congrArg (fun xs => xs[i]) w
    simpa using w
  · rintro rfl
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

@[simp] theorem getElem?_eq_none_iff {xs : Vector α n} : xs[i]? = none ↔ n ≤ i := by
  by_cases h : i < n
  · simp [getElem?_pos, h]
  · rw [getElem?_neg xs i h]
    simp_all

@[simp] theorem none_eq_getElem?_iff {xs : Vector α n} {i : Nat} : none = xs[i]? ↔ n ≤ i := by
  simp [eq_comm (a := none)]

theorem getElem?_eq_none {xs : Vector α n} (h : n ≤ i) : xs[i]? = none := by
  simp [getElem?_eq_none_iff, h]

@[simp] theorem getElem?_eq_getElem {xs : Vector α n} {i : Nat} (h : i < n) : xs[i]? = some xs[i] :=
  getElem?_pos ..

theorem getElem?_eq_some_iff {xs : Vector α n} : xs[i]? = some b ↔ ∃ h : i < n, xs[i] = b := by
  simp [getElem?_def]

theorem some_eq_getElem?_iff {xs : Vector α n} : some b = xs[i]? ↔ ∃ h : i < n, xs[i] = b := by
  rw [eq_comm, getElem?_eq_some_iff]

@[simp] theorem some_getElem_eq_getElem?_iff (xs : Vector α n) (i : Nat) (h : i < n) :
    (some xs[i] = xs[i]?) ↔ True := by
  simp [h]

@[simp] theorem getElem?_eq_some_getElem_iff (xs : Vector α n) (i : Nat) (h : i < n) :
    (xs[i]? = some xs[i]) ↔ True := by
  simp [h]

theorem getElem_eq_iff {xs : Vector α n} {i : Nat} {h : i < n} : xs[i] = x ↔ xs[i]? = some x := by
  simp only [getElem?_eq_some_iff]
  exact ⟨fun w => ⟨h, w⟩, fun h => h.2⟩

theorem getElem_eq_getElem?_get (xs : Vector α n) (i : Nat) (h : i < n) :
    xs[i] = xs[i]?.get (by simp [getElem?_eq_getElem, h]) := by
  simp [getElem_eq_iff]

theorem getD_getElem? (xs : Vector α n) (i : Nat) (d : α) :
    xs[i]?.getD d = if p : i < n then xs[i]'p else d := by
  if h : i < n then
    simp [h, getElem?_def]
  else
    have p : i ≥ n := Nat.le_of_not_gt h
    simp [getElem?_eq_none p, h]

@[simp] theorem getElem?_empty {i : Nat} : (#v[] : Vector α 0)[i]? = none := rfl

@[simp] theorem getElem_push_lt {xs : Vector α n} {x : α} {i : Nat} (h : i < n) :
    (xs.push x)[i] = xs[i] := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem_push_lt, h]

set_option linter.indexVariables false in
@[simp] theorem getElem_push_eq {xs : Vector α n} {x : α} : (xs.push x)[n] = x := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem getElem_push {xs : Vector α n} {x : α} {i : Nat} (h : i < n + 1) :
    (xs.push x)[i] = if h : i < n then xs[i] else x := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem_push, h]

theorem getElem?_push {xs : Vector α n} {x : α} {i : Nat} : (xs.push x)[i]? = if i = n then some x else xs[i]? := by
  simp [getElem?_def, getElem_push]
  (repeat' split) <;> first | rfl | omega

set_option linter.indexVariables false in
@[simp] theorem getElem?_push_size {xs : Vector α n} {x : α} : (xs.push x)[n]? = some x := by
  simp [getElem?_push]

@[simp] theorem getElem_singleton (a : α) (h : i < 1) : #v[a][i] = a :=
  match i, h with
  | 0, _ => rfl

theorem getElem?_singleton (a : α) (i : Nat) : #v[a][i]? = if i = 0 then some a else none := by
  simp [List.getElem?_singleton]

/-! ### mem -/

@[simp] theorem getElem_mem {xs : Vector α n} {i : Nat} (h : i < n) : xs[i] ∈ xs := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem not_mem_empty (a : α) : ¬ a ∈ #v[] := nofun

@[simp] theorem mem_push {xs : Vector α n} {x y : α} : x ∈ xs.push y ↔ x ∈ xs ∨ x = y := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem mem_push_self {xs : Vector α n} {x : α} : x ∈ xs.push x :=
  mem_push.2 (Or.inr rfl)

theorem eq_push_append_of_mem {xs : Vector α n} {x : α} (h : x ∈ xs) :
    ∃ (n₁ n₂ : Nat) (as : Vector α n₁) (bs : Vector α n₂) (h : n₁ + 1 + n₂ = n),
      xs = (as.push x ++ bs).cast h ∧ x ∉ as:= by
  rcases xs with ⟨xs, rfl⟩
  obtain ⟨as, bs, h, w⟩ := Array.eq_push_append_of_mem (by simpa using h)
  simp only at h
  obtain rfl := h
  exact ⟨_, _, as.toVector, bs.toVector, by simp, by simp, by simpa using w⟩

theorem mem_push_of_mem {xs : Vector α n} {x : α} (y : α) (h : x ∈ xs) : x ∈ xs.push y :=
  mem_push.2 (Or.inl h)

theorem exists_mem_of_size_pos (xs : Vector α n) (h : 0 < n) : ∃ x, x ∈ xs := by
  simpa using List.exists_mem_of_ne_nil xs.toList (by simpa using (Nat.ne_of_gt h))

theorem size_zero_iff_forall_not_mem {xs : Vector α n} : n = 0 ↔ ∀ a, a ∉ xs := by
  simpa using List.eq_nil_iff_forall_not_mem (l := xs.toList)

@[simp] theorem mem_dite_empty_left {x : α} [Decidable p] {xs : ¬ p → Vector α 0} :
    (x ∈ if h : p then #v[] else xs h) ↔ ∃ h : ¬ p, x ∈ xs h := by
  split <;> simp_all

@[simp] theorem mem_dite_empty_right {x : α} [Decidable p] {xs : p → Vector α 0} :
    (x ∈ if h : p then xs h else #v[]) ↔ ∃ h : p, x ∈ xs h := by
  split <;> simp_all

@[simp] theorem mem_ite_empty_left {x : α} [Decidable p] {xs : Vector α 0} :
    (x ∈ if p then #v[] else xs) ↔ ¬ p ∧ x ∈ xs := by
  split <;> simp_all

@[simp] theorem mem_ite_empty_right {x : α} [Decidable p] {xs : Vector α 0} :
    (x ∈ if p then xs else #v[]) ↔ p ∧ x ∈ xs := by
  split <;> simp_all

theorem eq_of_mem_singleton (h : a ∈ #v[b]) : a = b := by
  simpa using h

@[simp] theorem mem_singleton {a b : α} : a ∈ #v[b] ↔ a = b :=
  ⟨eq_of_mem_singleton, (by simp [·])⟩

theorem forall_mem_push {p : α → Prop} {xs : Vector α n} {a : α} :
    (∀ x, x ∈ xs.push a → p x) ↔ p a ∧ ∀ x, x ∈ xs → p x := by
  cases xs
  simp [or_comm, forall_eq_or_imp]

theorem forall_mem_ne {a : α} {xs : Vector α n} : (∀ a' : α, a' ∈ xs → ¬a = a') ↔ a ∉ xs :=
  ⟨fun h m => h _ m rfl, fun h _ m e => h (e.symm ▸ m)⟩

theorem forall_mem_ne' {a : α} {xs : Vector α n} : (∀ a' : α, a' ∈ xs → ¬a' = a) ↔ a ∉ xs :=
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

theorem mem_of_mem_push_of_mem {a b : α} {xs : Vector α n} : a ∈ xs.push b → b ∈ xs → a ∈ xs := by
  rcases xs with ⟨xs, rfl⟩
  simpa using Array.mem_of_mem_push_of_mem

theorem eq_or_ne_mem_of_mem {a b : α} {xs : Vector α n} (h' : a ∈ xs.push b) :
    a = b ∨ (a ≠ b ∧ a ∈ xs) := by
  if h : a = b then
    exact .inl h
  else
    simp only [mem_push, h, or_false] at h'
    exact .inr ⟨h, h'⟩

theorem size_ne_zero_of_mem {a : α} {xs : Vector α n} (h : a ∈ xs) : n ≠ 0 := by
  rcases xs with ⟨xs, rfl⟩
  simpa using Array.ne_empty_of_mem (by simpa using h)

theorem mem_of_ne_of_mem {a y : α} {xs : Vector α n} (h₁ : a ≠ y) (h₂ : a ∈ xs.push y) : a ∈ xs := by
  simpa [h₁] using h₂

theorem ne_of_not_mem_push {a b : α} {xs : Vector α n} (h : a ∉ xs.push b) : a ≠ b := by
  simp only [mem_push, not_or] at h
  exact h.2

theorem not_mem_of_not_mem_push {a b : α} {xs : Vector α n} (h : a ∉ xs.push b) : a ∉ xs := by
  simp only [mem_push, not_or] at h
  exact h.1

theorem not_mem_push_of_ne_of_not_mem {a y : α} {xs : Vector α n} : a ≠ y → a ∉ xs → a ∉ xs.push y :=
  mt ∘ mem_of_ne_of_mem

theorem ne_and_not_mem_of_not_mem_push {a y : α} {xs : Vector α n} : a ∉ xs.push y → a ≠ y ∧ a ∉ xs := by
  simp +contextual

theorem getElem_of_mem {a} {xs : Vector α n} (h : a ∈ xs) : ∃ (i : Nat) (h : i < n), xs[i]'h = a := by
  rcases xs with ⟨xs, rfl⟩
  simpa using Array.getElem_of_mem (by simpa using h)

theorem getElem?_of_mem {a} {xs : Vector α n} (h : a ∈ xs) : ∃ i : Nat, xs[i]? = some a :=
  let ⟨n, _, e⟩ := getElem_of_mem h; ⟨n, e ▸ getElem?_eq_getElem _⟩

theorem mem_of_getElem {xs : Vector α n} {i : Nat} {h} {a : α} (e : xs[i] = a) : a ∈ xs := by
  subst e
  simp

theorem mem_of_getElem? {xs : Vector α n} {i : Nat} {a : α} (e : xs[i]? = some a) : a ∈ xs :=
  let ⟨_, e⟩ := getElem?_eq_some_iff.1 e; e ▸ getElem_mem ..

theorem mem_of_back? {xs : Vector α n} {a : α} (h : xs.back? = some a) : a ∈ xs := by
  cases xs
  simpa using Array.mem_of_back? (by simpa using h)

theorem mem_iff_getElem {a} {xs : Vector α n} : a ∈ xs ↔ ∃ (i : Nat) (h : i < n), xs[i]'h = a :=
  ⟨getElem_of_mem, fun ⟨_, _, e⟩ => e ▸ getElem_mem ..⟩

theorem mem_iff_getElem? {a} {xs : Vector α n} : a ∈ xs ↔ ∃ i : Nat, xs[i]? = some a := by
  simp [getElem?_eq_some_iff, mem_iff_getElem]

theorem forall_getElem {xs : Vector α n} {p : α → Prop} :
    (∀ (i : Nat) h, p (xs[i]'h)) ↔ ∀ a, a ∈ xs → p a := by
  rcases xs with ⟨xs, rfl⟩
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

@[simp] theorem contains_push [BEq α] {xs : Vector α n} {a : α} {b : α} :
    (xs.push a).contains b = (xs.contains b || b == a) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.contains_push]

/-! ### set -/

theorem getElem_set (xs : Vector α n) (i : Nat) (x : α) (hi : i < n) (j : Nat) (hj : j < n) :
    (xs.set i x hi)[j] = if i = j then x else xs[j] := by
  cases xs
  split <;> simp_all [Array.getElem_set]

@[simp] theorem getElem_set_self (xs : Vector α n) (i : Nat) (x : α) (hi : i < n) :
    (xs.set i x hi)[i] = x := by simp [getElem_set]

@[deprecated getElem_set_self (since := "2024-12-12")]
abbrev getElem_set_eq := @getElem_set_self

@[simp] theorem getElem_set_ne (xs : Vector α n) (i : Nat) (x : α) (hi : i < n) (j : Nat)
    (hj : j < n) (h : i ≠ j) : (xs.set i x hi)[j] = xs[j] := by simp [getElem_set, h]

theorem getElem?_set (xs : Vector α n) (i : Nat) (hi : i < n) (x : α) (j : Nat) :
    (xs.set i x hi)[j]? = if i = j then some x else xs[j]? := by
  cases xs
  split <;> simp_all [getElem?_eq_getElem, getElem_set]

@[simp] theorem getElem?_set_self (xs : Vector α n) (i : Nat) (hi : i < n) (x : α) :
    (xs.set i x hi)[i]? = some x := by simp [getElem?_eq_getElem, hi]

@[simp] theorem getElem?_set_ne (xs : Vector α n) (i : Nat) (hi : i < n) (x : α) (j : Nat)
    (h : i ≠ j) : (xs.set i x hi)[j]? = xs[j]? := by
  simp [getElem?_set, h]

@[simp] theorem set_getElem_self {xs : Vector α n} {i : Nat} (hi : i < n) :
    xs.set i xs[i] hi = xs := by
  cases xs
  simp

theorem set_comm (a b : α) {i j : Nat} (xs : Vector α n) {hi : i < n} {hj : j < n} (h : i ≠ j) :
    (xs.set i a hi).set j b hj = (xs.set j b hj).set i a hi := by
  cases xs
  simp [Array.set_comm, h]

@[simp] theorem set_set (a b : α) (xs : Vector α n) (i : Nat) (hi : i < n) :
    (xs.set i a hi).set i b hi = xs.set i b hi := by
  cases xs
  simp

theorem mem_set (xs : Vector α n) (i : Nat) (hi : i < n) (a : α) :
    a ∈ xs.set i a hi := by
  simp [mem_iff_getElem]
  exact ⟨i, (by simpa using hi), by simp⟩

theorem mem_or_eq_of_mem_set {xs : Vector α n} {i : Nat} {a b : α} {hi : i < n} (h : a ∈ xs.set i b) : a ∈ xs ∨ a = b := by
  cases xs
  simpa using Array.mem_or_eq_of_mem_set (by simpa using h)

/-! ### setIfInBounds -/

theorem getElem_setIfInBounds (xs : Vector α n) (i : Nat) (x : α) (j : Nat)
    (hj : j < n) : (xs.setIfInBounds i x)[j] = if i = j then x else xs[j] := by
  cases xs
  split <;> simp_all [Array.getElem_setIfInBounds]

@[simp] theorem getElem_setIfInBounds_self (xs : Vector α n) (i : Nat) (x : α) (hi : i < n) :
    (xs.setIfInBounds i x)[i] = x := by simp [getElem_setIfInBounds, hi]

@[deprecated getElem_setIfInBounds_self (since := "2024-12-12")]
abbrev getElem_setIfInBounds_eq := @getElem_setIfInBounds_self

@[simp] theorem getElem_setIfInBounds_ne (xs : Vector α n) (i : Nat) (x : α) (j : Nat)
    (hj : j < n) (h : i ≠ j) : (xs.setIfInBounds i x)[j] = xs[j] := by simp [getElem_setIfInBounds, h]

theorem getElem?_setIfInBounds (xs : Vector α n) (i : Nat) (x : α) (j : Nat) :
    (xs.setIfInBounds i x)[j]? = if i = j then if i < n then some x else none else xs[j]? := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem?_setIfInBounds]

theorem getElem?_setIfInBounds_self (xs : Vector α n) (i : Nat) (x : α) :
    (xs.setIfInBounds i x)[i]? = if i < n then some x else none := by simp [getElem?_setIfInBounds]

@[simp] theorem getElem?_setIfInBounds_self_of_lt (xs : Vector α n) (i : Nat) (x : α) (h : i < n) :
    (xs.setIfInBounds i x)[i]? = some x := by simp [getElem?_setIfInBounds, h]

@[simp] theorem getElem?_setIfInBounds_ne (xs : Vector α n) (i : Nat) (x : α) (j : Nat)
    (h : i ≠ j) : (xs.setIfInBounds i x)[j]? = xs[j]? := by simp [getElem?_setIfInBounds, h]

theorem setIfInBounds_eq_of_size_le {xs : Vector α n} {i : Nat} (h : xs.size ≤ i) {a : α} :
    xs.setIfInBounds i a = xs := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.setIfInBounds_eq_of_size_le (by simpa using h)]

theorem setIfInBound_comm (a b : α) {i j : Nat} (xs : Vector α n) (h : i ≠ j) :
    (xs.setIfInBounds i a).setIfInBounds j b = (xs.setIfInBounds j b).setIfInBounds i a := by
  rcases xs with ⟨xs, rfl⟩
  simp only [setIfInBounds_mk, mk.injEq]
  rw [Array.setIfInBounds_comm _ _ _ h]

@[simp] theorem setIfInBounds_setIfInBounds (a b : α) (xs : Vector α n) (i : Nat) :
    (xs.setIfInBounds i a).setIfInBounds i b = xs.setIfInBounds i b := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem mem_setIfInBounds (xs : Vector α n) (i : Nat) (hi : i < n) (a : α) :
    a ∈ xs.setIfInBounds i a := by
  simp [mem_iff_getElem]
  exact ⟨i, (by simpa using hi), by simp⟩

/-! ### BEq -/

@[simp] theorem push_beq_push [BEq α] {a b : α} {n : Nat} {xs : Vector α n} {ys : Vector α n} :
    (xs.push a == ys.push b) = (xs == ys && a == b) := by
  cases xs
  cases ys
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
      rintro ⟨xs, h⟩
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
      · rintro ⟨as, ha⟩ ⟨bs, hb⟩ h
        simp_all
      · rintro ⟨as, ha⟩
        simp

/-! ### isEqv -/

@[simp] theorem isEqv_eq [DecidableEq α] {xs ys : Vector α n} : xs.isEqv ys (· == ·) = (xs = ys) := by
  cases xs
  cases ys
  simp

/-! ### back -/

theorem back_eq_getElem [NeZero n] (xs : Vector α n) : xs.back = xs[n - 1]'(by have := NeZero.ne n; omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.back_eq_getElem]

theorem back?_eq_getElem? (xs : Vector α n) : xs.back? = xs[n - 1]? := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.back?_eq_getElem?]

@[simp] theorem back_mem [NeZero n] {xs : Vector α n} : xs.back ∈ xs := by
  cases xs
  simp

/-! ### map -/

@[simp] theorem getElem_map (f : α → β) (xs : Vector α n) (i : Nat) (hi : i < n) :
    (xs.map f)[i] = f xs[i] := by
  cases xs
  simp

@[simp] theorem getElem?_map (f : α → β) (xs : Vector α n) (i : Nat) :
    (xs.map f)[i]? = xs[i]?.map f := by
  cases xs
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
  funext xs
  induction xs <;> simp_all

/-- `map_id_fun'` differs from `map_id_fun` by representing the identity function as a lambda, rather than `id`. -/
@[simp] theorem map_id_fun' : map (n := n) (fun (a : α) => a) = id := map_id_fun

-- This is not a `@[simp]` lemma because `map_id_fun` will apply.
theorem map_id (xs : Vector α n) : map (id : α → α) xs = xs := by
  cases xs <;> simp_all

/-- `map_id'` differs from `map_id` by representing the identity function as a lambda, rather than `id`. -/
-- This is not a `@[simp]` lemma because `map_id_fun'` will apply.
theorem map_id' (xs : Vector α n) : map (fun (a : α) => a) xs = xs := map_id xs

/-- Variant of `map_id`, with a side condition that the function is pointwise the identity. -/
theorem map_id'' {f : α → α} (h : ∀ x, f x = x) (xs : Vector α n) : map f xs = xs := by
  simp [show f = id from funext h]

theorem map_singleton (f : α → β) (a : α) : map f #v[a] = #v[f a] := rfl

-- We use a lower priority here as there are more specific lemmas in downstream libraries
-- which should be able to fire first.
@[simp 500] theorem mem_map {f : α → β} {xs : Vector α n} : b ∈ xs.map f ↔ ∃ a, a ∈ xs ∧ f a = b := by
  cases xs
  simp

theorem exists_of_mem_map (h : b ∈ map f xs) : ∃ a, a ∈ xs ∧ f a = b := mem_map.1 h

theorem mem_map_of_mem (f : α → β) (h : a ∈ xs) : f a ∈ map f xs := mem_map.2 ⟨_, h, rfl⟩

theorem forall_mem_map {f : α → β} {xs : Vector α n} {P : β → Prop} :
    (∀ (i) (_ : i ∈ xs.map f), P i) ↔ ∀ (j) (_ : j ∈ xs), P (f j) := by
  simp

@[simp] theorem map_inj_left {f g : α → β} : map f xs = map g xs ↔ ∀ a ∈ xs, f a = g a := by
  cases xs <;> simp_all

theorem map_inj_right {f : α → β} (w : ∀ x y, f x = f y → x = y) : map f xs = map f ys ↔ xs = ys := by
  cases xs
  cases ys
  simp [Array.map_inj_right w]

theorem map_congr_left (h : ∀ a ∈ xs, f a = g a) : map f xs = map g xs :=
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

theorem map_eq_push_iff {f : α → β} {xs : Vector α (n + 1)} {ys : Vector β n} {b : β} :
    map f xs = ys.push b ↔ ∃ xs' a, xs = xs'.push a ∧ map f xs' = ys ∧ f a = b := by
  rcases xs with ⟨xs, h⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [map_mk, push_mk, mk.injEq, Array.map_eq_push_iff]
  constructor
  · rintro ⟨xs', a, rfl, rfl, rfl⟩
    refine ⟨⟨xs', by simp⟩, a, by simp⟩
  · rintro ⟨xs', a, h₁, h₂, rfl⟩
    refine ⟨xs'.toArray, a, by simp_all⟩

@[simp] theorem map_eq_singleton_iff {f : α → β} {xs : Vector α 1} {b : β} :
    map f xs = #v[b] ↔ ∃ a, xs = #v[a] ∧ f a = b := by
  cases xs
  simp

theorem map_eq_map_iff {f g : α → β} {xs : Vector α n} :
    map f xs = map g xs ↔ ∀ a ∈ xs, f a = g a := by
  cases xs <;> simp_all

theorem map_eq_iff {f : α → β} {as : Vector α n} {bs : Vector β n} :
    map f as = bs ↔ ∀ i (h : i < n), bs[i] = f as[i] := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, h'⟩
  simp only [map_mk, eq_mk, Array.map_eq_iff, getElem_mk]
  constructor
  · intro w i h
    simpa [h, h'] using w i
  · intro w i
    if h : i < as.size then
      simpa [h, h'] using w i h
    else
      rw [getElem?_neg, getElem?_neg, Option.map_none'] <;> omega

@[simp] theorem map_set {f : α → β} {xs : Vector α n} {i : Nat} {h : i < n} {a : α} :
    (xs.set i a).map f = (xs.map f).set i (f a) (by simpa using h) := by
  cases xs
  simp

@[simp] theorem map_setIfInBounds {f : α → β} {xs : Vector α n} {i : Nat} {a : α} :
    (xs.setIfInBounds i a).map f = (xs.map f).setIfInBounds i (f a) := by
  cases xs
  simp

@[simp] theorem map_pop {f : α → β} {xs : Vector α n} : xs.pop.map f = (xs.map f).pop := by
  cases xs
  simp

@[simp] theorem back?_map {f : α → β} {xs : Vector α n} : (xs.map f).back? = xs.back?.map f := by
  cases xs
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
    (xss : Vector (Vector α n) m) : P xss := by
  specialize of (xss.map toArray).toArray (by simp) (by simp)
  simpa [Array.map_attach_eq_pmap, Array.pmap_map] using of

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
      (h₃ : ∀ xs ∈ xss, ∀ as ∈ xs, as.size = n),
      P (mk (xss.attach.map (fun ⟨xs, m⟩ =>
        mk (xs.attach.map (fun ⟨as, m'⟩ =>
          mk as (h₃ xs m as m'))) (by simpa using h₂ xs m))) (by simpa using h₁)))
    (xss : Vector (Vector (Vector α n) m) k) : P xss := by
  specialize of (xss.map (fun as => (as.map toArray).toArray)).toArray (by simp) (by simp) (by simp)
  simpa [Array.map_attach_eq_pmap, Array.pmap_map] using of

/-! ### singleton -/

@[simp] theorem singleton_def (v : α) : Vector.singleton v = #v[v] := rfl

/-! ### append -/

@[simp] theorem append_push {as : Vector α n} {bs : Vector α m} {a : α} :
    as ++ bs.push a = (as ++ bs).push a := by
  cases as
  cases bs
  simp

theorem singleton_eq_toVector_singleton (a : α) : #v[a] = #[a].toVector := rfl

@[simp] theorem mem_append {a : α} {xs : Vector α n} {ys : Vector α m} :
    a ∈ xs ++ ys ↔ a ∈ xs ∨ a ∈ ys := by
  cases xs
  cases ys
  simp

theorem mem_append_left {a : α} {xs : Vector α n} (ys : Vector α m) (h : a ∈ xs) : a ∈ xs ++ ys :=
  mem_append.2 (Or.inl h)

theorem mem_append_right {a : α} (xs : Vector α n) {ys : Vector α m} (h : a ∈ ys) : a ∈ xs ++ ys :=
  mem_append.2 (Or.inr h)

theorem not_mem_append {a : α} {xs : Vector α n} {ys : Vector α m} (h₁ : a ∉ xs) (h₂ : a ∉ ys) :
    a ∉ xs ++ ys :=
  mt mem_append.1 $ not_or.mpr ⟨h₁, h₂⟩

/--
See also `eq_push_append_of_mem`, which proves a stronger version
in which the initial array must not contain the element.
-/
theorem append_of_mem {a : α} {xs : Vector α n} (h : a ∈ xs) :
    ∃ (m k : Nat) (w : m + 1 + k = n) (ys : Vector α m) (zs : Vector α k),
      xs = (ys.push a ++ zs).cast w := by
  rcases xs with ⟨xs, rfl⟩
  obtain ⟨ys, zs, rfl⟩ := Array.append_of_mem (by simpa using h)
  refine ⟨_, _, by simp, ys.toVector, zs.toVector, by simp_all⟩

theorem mem_iff_append {a : α} {xs : Vector α n} :
    a ∈ xs ↔ ∃ (m k : Nat) (w : m + 1 + k = n) (ys : Vector α m) (zs : Vector α k),
      xs = (ys.push a ++ zs).cast w :=
  ⟨append_of_mem, by rintro ⟨m, k, rfl, ys, zs, rfl⟩; simp⟩

theorem forall_mem_append {p : α → Prop} {xs : Vector α n} {ys : Vector α m} :
    (∀ (x) (_ : x ∈ xs ++ ys), p x) ↔ (∀ (x) (_ : x ∈ xs), p x) ∧ (∀ (x) (_ : x ∈ ys), p x) := by
  simp only [mem_append, or_imp, forall_and]

theorem empty_append (xs : Vector α n) : (#v[] : Vector α 0) ++ xs = xs.cast (by omega) := by
  rcases xs with ⟨as, rfl⟩
  simp

theorem append_empty (xs : Vector α n) : xs ++ (#v[] : Vector α 0) = xs := by
  rw [← toArray_inj, toArray_append, Array.append_empty]

theorem getElem_append (xs : Vector α n) (ys : Vector α m) (i : Nat) (hi : i < n + m) :
    (xs ++ ys)[i] = if h : i < n then xs[i] else ys[i - n] := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.getElem_append, hi]

theorem getElem_append_left {xs : Vector α n} {ys : Vector α m} {i : Nat} (hi : i < n) :
    (xs ++ ys)[i] = xs[i] := by simp [getElem_append, hi]

theorem getElem_append_right {xs : Vector α n} {ys : Vector α m} {i : Nat} (h : i < n + m) (hi : n ≤ i) :
    (xs ++ ys)[i] = ys[i - n] := by
  rw [getElem_append, dif_neg (by omega)]

theorem getElem?_append_left {xs : Vector α n} {ys : Vector α m} {i : Nat} (hn : i < n) :
    (xs ++ ys)[i]? = xs[i]? := by
  have hn' : i < n + m := by omega
  simp_all [getElem?_eq_getElem, getElem_append]

theorem getElem?_append_right {xs : Vector α n} {ys : Vector α m} {i : Nat} (h : n ≤ i) :
    (xs ++ ys)[i]? = ys[i - n]? := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.getElem?_append_right, h]

theorem getElem?_append {xs : Vector α n} {ys : Vector α m} {i : Nat} :
    (xs ++ ys)[i]? = if i < n then xs[i]? else ys[i - n]? := by
  split <;> rename_i h
  · exact getElem?_append_left h
  · exact getElem?_append_right (by simpa using h)

/-- Variant of `getElem_append_left` useful for rewriting from the small array to the big array. -/
theorem getElem_append_left' (xs : Vector α m) {ys : Vector α n} {i : Nat} (hi : i < m) :
    xs[i] = (xs ++ ys)[i] := by
  rw [getElem_append_left] <;> simp

/-- Variant of `getElem_append_right` useful for rewriting from the small array to the big array. -/
theorem getElem_append_right' (xs : Vector α m) {ys : Vector α n} {i : Nat} (hi : i < n) :
    ys[i] = (xs ++ ys)[i + m] := by
  rw [getElem_append_right] <;> simp [*, Nat.le_add_left]

set_option linter.indexVariables false in
theorem getElem_of_append {xs : Vector α n} {xs₁ : Vector α m} {xs₂ : Vector α k}
    (w : m + 1 + k = n) (eq : xs = (xs₁.push a ++ xs₂).cast w) :
    xs[m] = a := Option.some.inj <| by
  rw [← getElem?_eq_getElem, eq, getElem?_cast, getElem?_append_left (by simp)]
  simp

@[simp] theorem append_singleton {a : α} {xs : Vector α n} : xs ++ #v[a] = xs.push a := by
  cases xs
  simp

theorem append_inj {xs₁ xs₂ : Vector α n} {ys₁ ys₂ : Vector α m} (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) :
    xs₁ = xs₂ ∧ ys₁ = ys₂ := by
  rcases xs₁ with ⟨xs₁, rfl⟩
  rcases xs₂ with ⟨xs₂, hx⟩
  rcases ys₁ with ⟨ys₁, rfl⟩
  rcases ys₂ with ⟨ys₂, hy⟩
  simpa using Array.append_inj (by simpa using h) (by omega)

theorem append_inj_right {xs₁ xs₂ : Vector α n} {ys₁ ys₂ : Vector α m}
    (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) : ys₁ = ys₂ :=
  (append_inj h).right

theorem append_inj_left {xs₁ xs₂ : Vector α n} {ys₁ ys₂ : Vector α m}
    (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) : xs₁ = xs₂ :=
  (append_inj h).left

theorem append_right_inj {ys₁ ys₂ : Vector α m} (xs : Vector α n) : xs ++ ys₁ = xs ++ ys₂ ↔ ys₁ = ys₂ :=
  ⟨fun h => append_inj_right h, congrArg _⟩

theorem append_left_inj {xs₁ xs₂ : Vector α n} (ys : Vector α m) : xs₁ ++ ys = xs₂ ++ ys ↔ xs₁ = xs₂ :=
  ⟨fun h => append_inj_left h, congrArg (· ++ _)⟩

theorem append_eq_append_iff {ws : Vector α n} {xs : Vector α m} {ys : Vector α k} {zs : Vector α l}
    (w : k + l = n + m) :
    ws ++ xs = (ys ++ zs).cast w ↔
      if h : n ≤ k then
        ∃ as : Vector α (k - n), ys = (ws ++ as).cast (by omega) ∧ xs = (as ++ zs).cast (by omega)
      else
        ∃ cs : Vector α (n - k), ws = (ys ++ cs).cast (by omega) ∧ zs = (cs ++ xs).cast (by omega) := by
  rcases ws with ⟨ws, rfl⟩
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  rcases zs with ⟨zs, rfl⟩
  simp only [mk_append_mk, Array.append_eq_append_iff, mk_eq, toArray_cast]
  constructor
  · rintro (⟨as, rfl, rfl⟩ | ⟨cs, rfl, rfl⟩)
    · rw [dif_pos (by simp)]
      exact ⟨as.toVector.cast (by simp; omega), by simp⟩
    · split <;> rename_i h
      · have hc : cs.size = 0 := by simp at h; omega
        simp at hc
        exact ⟨#v[].cast (by simp; omega), by simp_all⟩
      · exact ⟨cs.toVector.cast (by simp; omega), by simp⟩
  · split <;> rename_i h
    · rintro ⟨as, hc, rfl⟩
      left
      refine ⟨as.toArray, hc, rfl⟩
    · rintro ⟨cs, ha, rfl⟩
      right
      refine ⟨cs.toArray, ha, rfl⟩

theorem set_append {xs : Vector α n} {ys : Vector α m} {i : Nat} {x : α} (h : i < n + m) :
    (xs ++ ys).set i x =
      if h' : i < n then
        xs.set i x ++ ys
      else
        xs ++ ys.set (i - n) x := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [mk_append_mk, set_mk, Array.set_append]
  split <;> simp

@[simp] theorem set_append_left {xs : Vector α n} {ys : Vector α m} {i : Nat} {x : α} (h : i < n) :
    (xs ++ ys).set i x = xs.set i x ++ ys := by
  simp [set_append, h]

@[simp] theorem set_append_right {xs : Vector α n} {ys : Vector α m} {i : Nat} {x : α}
    (h' : i < n + m) (h : n ≤ i) :
    (xs ++ ys).set i x = xs ++ ys.set (i - n) x := by
  rw [set_append, dif_neg (by omega)]

theorem setIfInBounds_append {xs : Vector α n} {ys : Vector α m} {i : Nat} {x : α} :
    (xs ++ ys).setIfInBounds i x =
      if i < n then
        xs.setIfInBounds i x ++ ys
      else
        xs ++ ys.setIfInBounds (i - n) x := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [mk_append_mk, setIfInBounds_mk, Array.setIfInBounds_append]
  split <;> simp

@[simp] theorem setIfInBounds_append_left {xs : Vector α n} {ys : Vector α m} {i : Nat} {x : α} (h : i < n) :
    (xs ++ ys).setIfInBounds i x = xs.setIfInBounds i x ++ ys := by
  simp [setIfInBounds_append, h]

@[simp] theorem setIfInBounds_append_right {xs : Vector α n} {ys : Vector α m} {i : Nat} {x : α}
    (h : n ≤ i) :
    (xs ++ ys).setIfInBounds i x = xs ++ ys.setIfInBounds (i - n) x := by
  rw [setIfInBounds_append, if_neg (by omega)]

@[simp] theorem map_append (f : α → β) (xs : Vector α n) (ys : Vector α m) :
    map f (xs ++ ys) = map f xs ++ map f ys := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp

theorem map_eq_append_iff {f : α → β} :
    map f xs = ys ++ zs ↔ ∃ as bs, xs = as ++ bs ∧ map f as = ys ∧ map f bs = zs := by
  rcases xs with ⟨xs, h⟩
  rcases ys with ⟨ys, rfl⟩
  rcases zs with ⟨zs, rfl⟩
  simp only [map_mk, mk_append_mk, eq_mk, Array.map_eq_append_iff, mk_eq, toArray_append,
    toArray_map]
  constructor
  · rintro ⟨as, bs, rfl, rfl, rfl⟩
    exact ⟨as.toVector.cast (by simp), bs.toVector.cast (by simp), by simp⟩
  · rintro ⟨⟨as⟩, ⟨bs⟩, rfl, h₁, h₂⟩
    exact ⟨as, bs, by simp_all⟩

theorem append_eq_map_iff {f : α → β} :
    xs ++ ys = map f zs ↔ ∃ as bs, zs = as ++ bs ∧ map f as = xs ∧ map f bs = ys := by
  rw [eq_comm, map_eq_append_iff]

/-! ### flatten -/

set_option linter.listVariables false in
@[simp] theorem flatten_mk (xss : Array (Vector α n)) (h : xss.size = m) :
    (mk xss h).flatten =
      mk (xss.map toArray).flatten (by simp [Function.comp_def, Array.map_const', h]) := by
  simp [flatten]

@[simp] theorem getElem_flatten (xss : Vector (Vector β m) n) (i : Nat) (hi : i < n * m) :
    xss.flatten[i] =
      haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]
      haveI : i % m < m := Nat.mod_lt _ (Nat.pos_of_lt_mul_left hi)
      xss[i / m][i % m] := by
  rcases xss with ⟨⟨l⟩, rfl⟩
  simp only [flatten_mk, List.map_toArray, getElem_mk, List.getElem_toArray, Array.flatten_toArray]
  induction l generalizing i with
  | nil => simp at hi
  | cons xs l ih =>
    simp only [List.map_cons, List.map_map, List.flatten_cons]
    by_cases h : i < m
    · rw [List.getElem_append_left (by simpa)]
      have h₁ : i / m = 0 := Nat.div_eq_of_lt h
      have h₂ : i % m = i := Nat.mod_eq_of_lt h
      simp [h₁, h₂]
    · have h₁ : xs.toList.length ≤ i := by simp; omega
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

theorem getElem?_flatten (xss : Vector (Vector β m) n) (i : Nat) :
    xss.flatten[i]? =
      if hi : i < n * m then
        haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]
        haveI : i % m < m := Nat.mod_lt _ (Nat.pos_of_lt_mul_left hi)
        some xss[i / m][i % m]
      else
        none := by
  simp [getElem?_def]

@[simp] theorem flatten_singleton (xs : Vector α n) : #v[xs].flatten = xs.cast (by simp) := by
  simp [flatten]

set_option linter.listVariables false in
theorem mem_flatten {xss : Vector (Vector α n) m} : a ∈ xss.flatten ↔ ∃ xs, xs ∈ xss ∧ a ∈ xs := by
  rcases xss with ⟨xss, rfl⟩
  simp [Array.mem_flatten]
  constructor
  · rintro ⟨_, ⟨xs, h₁, rfl⟩, h₂⟩
    exact ⟨xs, h₁, by simpa using h₂⟩
  · rintro ⟨xs, h₁, h₂⟩
    exact ⟨xs.toArray, ⟨xs, h₁, rfl⟩, by simpa using h₂⟩

theorem exists_of_mem_flatten : xs ∈ flatten xss → ∃ ys, ys ∈ xss ∧ xs ∈ ys := mem_flatten.1

theorem mem_flatten_of_mem (ml : xs ∈ xss) (ma : a ∈ xs) : a ∈ flatten xss := mem_flatten.2 ⟨xs, ml, ma⟩

theorem forall_mem_flatten {p : α → Prop} {xss : Vector (Vector α n) m} :
    (∀ (x) (_ : x ∈ flatten xss), p x) ↔ ∀ (xs) (_ : xs ∈ xss) (x) (_ : x ∈ xs), p x := by
  simp only [mem_flatten, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

@[simp] theorem map_flatten (f : α → β) (xss : Vector (Vector α n) m) :
    (flatten xss).map f = (map (map f) xss).flatten := by
  induction xss using vector₂_induction with
  | of xss h₁ h₂ => simp

@[simp] theorem flatten_append (xss₁ : Vector (Vector α n) m₁) (xss₂ : Vector (Vector α n) m₂) :
    flatten (xss₁ ++ xss₂) = (flatten xss₁ ++ flatten xss₂).cast (by simp [Nat.add_mul]) := by
  induction xss₁ using vector₂_induction
  induction xss₂ using vector₂_induction
  simp

theorem flatten_push (xss : Vector (Vector α n) m) (xs : Vector α n) :
    flatten (xss.push xs) = (flatten xss ++ xs).cast (by simp [Nat.add_mul]) := by
  induction xss using vector₂_induction
  rcases xs with ⟨xs⟩
  simp [Array.flatten_push]

theorem flatten_flatten {xss : Vector (Vector (Vector α n) m) k} :
    flatten (flatten xss) = (flatten (map flatten xss)).cast (by simp [Nat.mul_assoc]) := by
  induction xss using vector₃_induction with
  | of xss h₁ h₂ h₃ =>
    -- simp [Array.flatten_flatten] -- FIXME: `simp` produces a bad proof here!
    simp [Array.map_attach_eq_pmap, Array.flatten_flatten, Array.map_pmap]

set_option linter.listVariables false in
/-- Two vectors of constant length vectors are equal iff their flattens coincide. -/
theorem eq_iff_flatten_eq {xss xss' : Vector (Vector α n) m} :
    xss = xss' ↔ xss.flatten = xss'.flatten := by
  induction xss using vector₂_induction with | of xss h₁ h₂ =>
  induction xss' using vector₂_induction with | of xss' h₁' h₂' =>
  simp only [eq_mk, flatten_mk, Array.map_map, Function.comp_apply, Array.map_subtype,
    Array.unattach_attach, Array.map_id_fun', id_eq]
  constructor
  · intro h
    suffices xss = xss' by simp_all
    apply Array.ext_getElem?
    intro i
    replace h := congrArg (fun xss => xss[i]?.map (fun xs => xs.toArray)) h
    simpa [Option.map_pmap] using h
  · intro h
    have w : xss.map Array.size = xss'.map Array.size := by
      ext i h h'
      · simp_all
      · simp only [Array.getElem_map]
        rw [h₂ _ (by simp), h₂' _ (by simp)]
    have := Array.eq_iff_flatten_eq.mpr ⟨h, w⟩
    subst this
    rfl


/-! ### flatMap -/

@[simp] theorem flatMap_toArray (xs : Vector α n) (f : α → Vector β m) :
    xs.toArray.flatMap (fun a => (f a).toArray) = (xs.flatMap f).toArray := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem flatMap_def (xs : Vector α n) (f : α → Vector β m) : xs.flatMap f = flatten (map f xs) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.flatMap_def, Function.comp_def]

@[simp] theorem getElem_flatMap (xs : Vector α n) (f : α → Vector β m) (i : Nat) (hi : i < n * m) :
    (xs.flatMap f)[i] =
      haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]
      haveI : i % m < m := Nat.mod_lt _ (Nat.pos_of_lt_mul_left hi)
      (f (xs[i / m]))[i % m] := by
  rw [flatMap_def, getElem_flatten, getElem_map]

theorem getElem?_flatMap (xs : Vector α n) (f : α → Vector β m) (i : Nat) :
    (xs.flatMap f)[i]? =
      if hi : i < n * m then
        haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]
        haveI : i % m < m := Nat.mod_lt _ (Nat.pos_of_lt_mul_left hi)
        some ((f (xs[i / m]))[i % m])
      else
        none := by
  simp [getElem?_def]

@[simp] theorem flatMap_id (xss : Vector (Vector α m) n) : xss.flatMap id = xss.flatten := by simp [flatMap_def]

@[simp] theorem flatMap_id' (xss : Vector (Vector α m) n) : xss.flatMap (fun xs => xs) = xss.flatten := by simp [flatMap_def]

@[simp] theorem mem_flatMap {f : α → Vector β m} {b} {xs : Vector α n} : b ∈ xs.flatMap f ↔ ∃ a, a ∈ xs ∧ b ∈ f a := by
  simp [flatMap_def, mem_flatten]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

theorem exists_of_mem_flatMap {b : β} {xs : Vector α n} {f : α → Vector β m} :
    b ∈ xs.flatMap f → ∃ a, a ∈ xs ∧ b ∈ f a := mem_flatMap.1

theorem mem_flatMap_of_mem {b : β} {xs : Vector α n} {f : α → Vector β m} {a} (al : a ∈ xs) (h : b ∈ f a) :
    b ∈ xs.flatMap f := mem_flatMap.2 ⟨a, al, h⟩

theorem forall_mem_flatMap {p : β → Prop} {xs : Vector α n} {f : α → Vector β m} :
    (∀ (x) (_ : x ∈ xs.flatMap f), p x) ↔ ∀ (a) (_ : a ∈ xs) (b) (_ : b ∈ f a), p b := by
  simp only [mem_flatMap, forall_exists_index, and_imp]
  constructor <;> (intros; solve_by_elim)

theorem flatMap_singleton (f : α → Vector β m) (x : α) : #v[x].flatMap f = (f x).cast (by simp) := by
  simp [flatMap_def]

@[simp] theorem flatMap_singleton' (xs : Vector α n) : (xs.flatMap fun x => #v[x]) = xs.cast (by simp) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem flatMap_append (xs ys : Vector α n) (f : α → Vector β m) :
    (xs ++ ys).flatMap f = (xs.flatMap f ++ ys.flatMap f).cast (by simp [Nat.add_mul]) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp [flatMap_def, flatten_append]

theorem flatMap_assoc {xs : Vector α n} (f : α → Vector β m) (g : β → Vector γ k) :
    (xs.flatMap f).flatMap g = (xs.flatMap fun x => (f x).flatMap g).cast (by simp [Nat.mul_assoc]) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.flatMap_assoc]

theorem map_flatMap (f : β → γ) (g : α → Vector β m) (xs : Vector α n) :
     (xs.flatMap g).map f = xs.flatMap fun a => (g a).map f := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.map_flatMap]

theorem flatMap_map (f : α → β) (g : β → Vector γ k) (xs : Vector α n) :
     (map f xs).flatMap g = xs.flatMap (fun a => g (f a)) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.flatMap_map]

theorem map_eq_flatMap {α β} (f : α → β) (xs : Vector α n) :
    map f xs = (xs.flatMap fun x => #v[f x]).cast (by simp) := by
  rcases xs with ⟨xs, rfl⟩
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

@[simp] theorem getElem?_mkVector_of_lt {n : Nat} {i : Nat} (h : i < n) : (mkVector n a)[i]? = some a := by
  simp [getElem?_mkVector, h]

theorem eq_mkVector_of_mem {a : α} {xs : Vector α n} (h : ∀ (b) (_ : b ∈ xs), b = a) : xs = mkVector n a := by
  rw [← toArray_inj]
  simpa using Array.eq_mkArray_of_mem (xs := xs.toArray) (by simpa using h)

theorem eq_mkVector_iff {a : α} {n} {xs : Vector α n} :
    xs = mkVector n a ↔ ∀ (b) (_ : b ∈ xs), b = a := by
  rw [← toArray_inj]
  simpa using Array.eq_mkArray_iff (xs := xs.toArray) (n := n)

theorem map_eq_mkVector_iff {xs : Vector α n} {f : α → β} {b : β} :
    xs.map f = mkVector n b ↔ ∀ x ∈ xs, f x = b := by
  simp [eq_mkVector_iff]

@[simp] theorem map_const (xs : Vector α n) (b : β) : map (Function.const α b) xs = mkVector n b :=
  map_eq_mkVector_iff.mpr fun _ _ => rfl

@[simp] theorem map_const_fun (x : β) : map (n := n) (Function.const α x) = fun _ => mkVector n x := by
  funext xs
  simp

/-- Variant of `map_const` using a lambda rather than `Function.const`. -/
-- This can not be a `@[simp]` lemma because it would fire on every `List.map`.
theorem map_const' (xs : Vector α n) (b : β) : map (fun _ => b) xs = mkVector n b :=
  map_const xs b

@[simp] theorem set_mkVector_self : (mkVector n a).set i a h = mkVector n a := by
  rw [← toArray_inj]
  simp

@[simp] theorem setIfInBounds_mkVector_self : (mkVector n a).setIfInBounds i a = mkVector n a := by
  rw [← toArray_inj]
  simp

@[simp] theorem mkVector_append_mkVector : mkVector n a ++ mkVector m a = mkVector (n + m) a := by
  rw [← toArray_inj]
  simp

theorem append_eq_mkVector_iff {xs : Vector α n} {ys : Vector α m} {a : α} :
    xs ++ ys = mkVector (n + m) a ↔ xs = mkVector n a ∧ ys = mkVector m a := by
  simp [← toArray_inj, Array.append_eq_mkArray_iff]

theorem mkVector_eq_append_iff {xs : Vector α n} {ys : Vector α m} {a : α} :
    mkVector (n + m) a = xs ++ ys ↔ xs = mkVector n a ∧ ys = mkVector m a := by
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

@[simp] theorem isEmpty_reverse {xs : Vector α n} : xs.reverse.isEmpty = xs.isEmpty := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem getElem_reverse (xs : Vector α n) (i : Nat) (hi : i < n) :
    (xs.reverse)[i] = xs[n - 1 - i] := by
  rcases xs with ⟨xs, rfl⟩
  simp

/-- Variant of `getElem?_reverse` with a hypothesis giving the linear relation between the indices. -/
theorem getElem?_reverse' {xs : Vector α n} (i j) (h : i + j + 1 = n) : xs.reverse[i]? = xs[j]? := by
  rcases xs with ⟨xs, rfl⟩
  simpa using Array.getElem?_reverse' i j h

@[simp]
theorem getElem?_reverse {xs : Vector α n} {i} (h : i < n) :
    xs.reverse[i]? = xs[n - 1 - i]? := by
  cases xs
  simp_all

@[simp] theorem reverse_reverse (xs : Vector α n) : xs.reverse.reverse = xs := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.reverse_reverse]

theorem reverse_eq_iff {xs ys : Vector α n} : xs.reverse = ys ↔ xs = ys.reverse := by
  constructor <;> (rintro rfl; simp)

@[simp] theorem reverse_inj {xs ys : Vector α n} : xs.reverse = ys.reverse ↔ xs = ys := by
  simp [reverse_eq_iff]

@[simp] theorem reverse_eq_push_iff {xs : Vector α (n + 1)} {ys : Vector α n} {a : α} :
    xs.reverse = ys.push a ↔ xs = (#v[a] ++ ys.reverse).cast (by omega) := by
  rcases xs with ⟨xs, h⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.reverse_eq_push_iff]

@[simp] theorem map_reverse (f : α → β) (xs : Vector α n) : xs.reverse.map f = (xs.map f).reverse := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.map_reverse]

@[simp] theorem reverse_append (xs : Vector α n) (ys : Vector α m) :
    (xs ++ ys).reverse = (ys.reverse ++ xs.reverse).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.reverse_append]

@[simp] theorem reverse_eq_append_iff {xs : Vector α (n + m)} {ys : Vector α n} {zs : Vector α m} :
    xs.reverse = ys ++ zs ↔ xs = (zs.reverse ++ ys.reverse).cast (by omega) := by
  cases xs
  cases ys
  cases zs
  simp

/-- Reversing a flatten is the same as reversing the order of parts and reversing all parts. -/
theorem reverse_flatten (xss : Vector (Vector α m) n) :
    xss.flatten.reverse = (xss.map reverse).reverse.flatten := by
  cases xss using vector₂_induction
  simp [Array.reverse_flatten]

/-- Flattening a reverse is the same as reversing all parts and reversing the flattened result. -/
theorem flatten_reverse (xss : Vector (Vector α m) n) :
    xss.reverse.flatten = (xss.map reverse).flatten.reverse := by
  cases xss using vector₂_induction
  simp [Array.flatten_reverse]

theorem reverse_flatMap {β} (xs : Vector α n) (f : α → Vector β m) :
    (xs.flatMap f).reverse = xs.reverse.flatMap (reverse ∘ f) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.reverse_flatMap, Function.comp_def]

theorem flatMap_reverse {β} (xs : Vector α n) (f : α → Vector β m) :
    (xs.reverse.flatMap f) = (xs.flatMap (reverse ∘ f)).reverse := by
  rcases xs with ⟨xs, rfl⟩
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
    (as.extract start stop)[i]? = if i < min stop n - start then as[start + i]? else none := by
  rcases as with ⟨as, rfl⟩
  simp [Array.getElem?_extract]

set_option linter.indexVariables false in
@[simp] theorem extract_size (as : Vector α n) : as.extract 0 n = as.cast (by simp) := by
  rcases as with ⟨as, rfl⟩
  simp

theorem extract_empty (start stop : Nat) :
    (#v[] : Vector α 0).extract start stop = #v[].cast (by simp) := by
  simp

/-! ### foldlM and foldrM -/

@[simp] theorem foldlM_append [Monad m] [LawfulMonad m] (f : β → α → m β) (b) (xs : Vector α n) (ys : Vector α k) :
    (xs ++ ys).foldlM f b = xs.foldlM f b >>= ys.foldlM f := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp

@[simp] theorem foldlM_empty [Monad m] (f : β → α → m β) (init : β) :
    foldlM f init #v[] = return init := by
  simp [foldlM]

@[simp] theorem foldrM_empty [Monad m] (f : α → β → m β) (init : β) :
    foldrM f init #v[] = return init := by
  simp [foldrM]

@[simp] theorem foldlM_push [Monad m] [LawfulMonad m] (xs : Vector α n) (a : α) (f : β → α → m β) (b) :
    (xs.push a).foldlM f b = xs.foldlM f b >>= fun b => f b a := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem foldl_eq_foldlM (f : β → α → β) (b) (xs : Vector α n) :
    xs.foldl f b = xs.foldlM (m := Id) f b := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldl_eq_foldlM]

theorem foldr_eq_foldrM (f : α → β → β) (b) (xs : Vector α n) :
    xs.foldr f b = xs.foldrM (m := Id) f b := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldr_eq_foldrM]

@[simp] theorem id_run_foldlM (f : β → α → Id β) (b) (xs : Vector α n) :
    Id.run (xs.foldlM f b) = xs.foldl f b := (foldl_eq_foldlM f b xs).symm

@[simp] theorem id_run_foldrM (f : α → β → Id β) (b) (xs : Vector α n) :
    Id.run (xs.foldrM f b) = xs.foldr f b := (foldr_eq_foldrM f b xs).symm

@[simp] theorem foldlM_reverse [Monad m] (xs : Vector α n) (f : β → α → m β) (b) :
    xs.reverse.foldlM f b = xs.foldrM (fun x y => f y x) b := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldlM_reverse]

@[simp] theorem foldrM_reverse [Monad m] (xs : Vector α n) (f : α → β → m β) (b) :
    xs.reverse.foldrM f b = xs.foldlM (fun x y => f y x) b := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem foldrM_push [Monad m] (f : α → β → m β) (init : β) (xs : Vector α n) (a : α) :
    (xs.push a).foldrM f init = f a init >>= xs.foldrM f := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldrM_push]

/-! ### foldl / foldr -/

@[congr]
theorem foldl_congr {xs ys : Vector α n} (h₀ : xs = ys) {f g : β → α → β} (h₁ : f = g)
     {a b : β} (h₂ : a = b) :
    xs.foldl f a = ys.foldl g b := by
  congr

@[congr]
theorem foldr_congr {xs ys : Vector α n} (h₀ : xs = ys) {f g : α → β → β} (h₁ : f = g)
     {a b : β} (h₂ : a = b) :
    xs.foldr f a = ys.foldr g b := by
  congr

@[simp] theorem foldr_push (f : α → β → β) (init : β) (xs : Vector α n) (a : α) :
    (xs.push a).foldr f init = xs.foldr f (f a init) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldr_push]

theorem foldl_map (f : β₁ → β₂) (g : α → β₂ → α) (xs : Vector β₁ n) (init : α) :
    (xs.map f).foldl g init = xs.foldl (fun x y => g x (f y)) init := by
  cases xs; simp [Array.foldl_map']

theorem foldr_map (f : α₁ → α₂) (g : α₂ → β → β) (xs : Vector α₁ n) (init : β) :
    (xs.map f).foldr g init = xs.foldr (fun x y => g (f x) y) init := by
  cases xs; simp [Array.foldr_map']

theorem foldl_filterMap (f : α → Option β) (g : γ → β → γ) (xs : Vector α n) (init : γ) :
    (xs.filterMap f).foldl g init = xs.foldl (fun x y => match f y with | some b => g x b | none => x) init := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldl_filterMap']
  rfl

theorem foldr_filterMap (f : α → Option β) (g : β → γ → γ) (xs : Vector α n) (init : γ) :
    (xs.filterMap f).foldr g init = xs.foldr (fun x y => match f x with | some b => g b y | none => y) init := by
  cases xs; simp [Array.foldr_filterMap']
  rfl

theorem foldl_map_hom (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (xs : Vector α n)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (xs.map g).foldl f' (g a) = g (xs.foldl f a) := by
  rcases xs with ⟨xs, rfl⟩
  simp
  rw [Array.foldl_map_hom' _ _ _ _ _ h rfl]

theorem foldr_map_hom (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (xs : Vector α n)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    (xs.map g).foldr f' (g a) = g (xs.foldr f a) := by
  rcases xs with ⟨xs, rfl⟩
  simp
  rw [Array.foldr_map_hom' _ _ _ _ _ h rfl]

@[simp] theorem foldrM_append [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (xs : Vector α n) (ys : Vector α k) :
    (xs ++ ys).foldrM f b = ys.foldrM f b >>= xs.foldrM f := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp

@[simp] theorem foldl_append {β : Type _} (f : β → α → β) (b) (xs : Vector α n) (ys : Vector α k) :
    (xs ++ ys).foldl f b = ys.foldl f (xs.foldl f b) := by simp [foldl_eq_foldlM]

@[simp] theorem foldr_append (f : α → β → β) (b) (xs : Vector α n) (ys : Vector α k) :
    (xs ++ ys).foldr f b = xs.foldr f (ys.foldr f b) := by simp [foldr_eq_foldrM]

@[simp] theorem foldl_flatten (f : β → α → β) (b : β) (xss : Vector (Vector α m) n) :
    (flatten xss).foldl f b = xss.foldl (fun b xs => xs.foldl f b) b := by
  cases xss using vector₂_induction
  simp [Array.foldl_flatten', Array.foldl_map']

@[simp] theorem foldr_flatten (f : α → β → β) (b : β) (xss : Vector (Vector α m) n) :
    (flatten xss).foldr f b = xss.foldr (fun xs b => xs.foldr f b) b := by
  cases xss using vector₂_induction
  simp [Array.foldr_flatten', Array.foldr_map']

@[simp] theorem foldl_reverse (xs : Vector α n) (f : β → α → β) (b) :
    xs.reverse.foldl f b = xs.foldr (fun x y => f y x) b := by simp [foldl_eq_foldlM, foldr_eq_foldrM]

@[simp] theorem foldr_reverse (xs : Vector α n) (f : α → β → β) (b) :
    xs.reverse.foldr f b = xs.foldl (fun x y => f y x) b :=
  (foldl_reverse ..).symm.trans <| by simp

theorem foldl_eq_foldr_reverse (xs : Vector α n) (f : β → α → β) (b) :
    xs.foldl f b = xs.reverse.foldr (fun x y => f y x) b := by simp

theorem foldr_eq_foldl_reverse (xs : Vector α n) (f : α → β → β) (b) :
    xs.foldr f b = xs.reverse.foldl (fun x y => f y x) b := by simp

theorem foldl_assoc {op : α → α → α} [ha : Std.Associative op] (xs : Vector α n) (a₁ a₂) :
    xs.foldl op (op a₁ a₂) = op a₁ (xs.foldl op a₂) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldl_assoc]

@[simp] theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op] (xs : Vector α n) (a₁ a₂) :
    xs.foldr op (op a₁ a₂) = op (xs.foldr op a₁) a₂ := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.foldr_assoc]

theorem foldl_hom (f : α₁ → α₂) (g₁ : α₁ → β → α₁) (g₂ : α₂ → β → α₂) (xs : Vector β n) (init : α₁)
    (H : ∀ x y, g₂ (f x) y = f (g₁ x y)) : xs.foldl g₂ (f init) = f (xs.foldl g₁ init) := by
  rcases xs with ⟨xs, rfl⟩
  simp
  rw [Array.foldl_hom _ _ _ _ _ H]

theorem foldr_hom (f : β₁ → β₂) (g₁ : α → β₁ → β₁) (g₂ : α → β₂ → β₂) (xs : Vector α n) (init : β₁)
    (H : ∀ x y, g₂ x (f y) = f (g₁ x y)) : xs.foldr g₂ (f init) = f (xs.foldr g₁ init) := by
  rcases xs with ⟨xs, rfl⟩
  simp
  rw [Array.foldr_hom _ _ _ _ _ H]

/--
We can prove that two folds over the same array are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the array,
preserves the relation.
-/
theorem foldl_rel {xs : Array α} {f g : β → α → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ xs → ∀ (c c' : β), r c c' → r (f c a) (g c' a)) :
    r (xs.foldl (fun acc a => f acc a) a) (xs.foldl (fun acc a => g acc a) b) := by
  rcases xs with ⟨xs⟩
  simpa using List.foldl_rel r h (by simpa using h')

/--
We can prove that two folds over the same array are related (by some arbitrary relation)
if we know that the initial elements are related and the folding function, for each element of the array,
preserves the relation.
-/
theorem foldr_rel {xs : Array α} {f g : α → β → β} {a b : β} (r : β → β → Prop)
    (h : r a b) (h' : ∀ (a : α), a ∈ xs → ∀ (c c' : β), r c c' → r (f a c) (g a c')) :
    r (xs.foldr (fun a acc => f a acc) a) (xs.foldr (fun a acc => g a acc) b) := by
  rcases xs with ⟨xs⟩
  simpa using List.foldr_rel r h (by simpa using h')

@[simp] theorem foldl_add_const (xs : Array α) (a b : Nat) :
    xs.foldl (fun x _ => x + a) b = b + a * xs.size := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem foldr_add_const (xs : Array α) (a b : Nat) :
    xs.foldr (fun _ x => x + a) b = b + a * xs.size := by
  rcases xs with ⟨xs⟩
  simp

/-! #### Further results about `back` and `back?` -/

@[simp] theorem back?_eq_none_iff {xs : Vector α n} : xs.back? = none ↔ n = 0 := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem back?_eq_some_iff {xs : Vector α n} {a : α} :
    xs.back? = some a ↔ ∃ (w : 0 < n)(ys : Vector α (n - 1)), xs = (ys.push a).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp only [back?_mk, Array.back?_eq_some_iff, mk_eq, toArray_cast, toArray_push]
  constructor
  · rintro ⟨ys, rfl⟩
    simp
    exact ⟨⟨ys, by simp⟩, by simp⟩
  · rintro ⟨w, ⟨ys, h₁⟩, h₂⟩
    exact ⟨ys, by simpa using h₂⟩

@[simp] theorem back?_isSome {xs : Vector α n} : xs.back?.isSome ↔ n ≠ 0 := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem back_append_of_neZero {xs : Vector α n} {ys : Vector α m} [NeZero m] :
    (xs ++ ys).back = ys.back := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [mk_append_mk, back_mk]
  rw [Array.back_append_of_size_pos]

theorem back_append {xs : Vector α n} {ys : Vector α m} [NeZero (n + m)] :
    (xs ++ ys).back =
      if h' : m = 0 then
        have : NeZero n := by subst h'; simp_all
        xs.back
      else
        have : NeZero m := ⟨h'⟩
        ys.back := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.back_append]
  split <;> rename_i h
  · rw [dif_pos]
    simp_all
  · rw [dif_neg]
    rwa [Array.isEmpty_iff_size_eq_zero] at h

theorem back_append_right {xs : Vector α n} {ys : Vector α m} [NeZero m] :
    (xs ++ ys).back = ys.back := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [mk_append_mk, back_mk]
  rw [Array.back_append_right]

theorem back_append_left {xs : Vector α n} {ys : Vector α 0} [NeZero n] :
    (xs ++ ys).back = xs.back := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  simp only [mk_append_mk, back_mk]
  rw [Array.back_append_left _ h]

@[simp] theorem back?_append {xs : Vector α n} {ys : Vector α m} : (xs ++ ys).back? = ys.back?.or xs.back? := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp

theorem back?_flatMap {xs : Vector α n} {f : α → Vector β m} :
    (xs.flatMap f).back? = xs.reverse.findSome? fun a => (f a).back? := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.back?_flatMap]
  rfl

set_option linter.listVariables false in -- This can probably be removed later.
theorem back?_flatten {xss : Vector (Vector α m) n} :
    (flatten xss).back? = xss.reverse.findSome? fun xs => xs.back? := by
  rcases xss with ⟨xss, rfl⟩
  simp [Array.back?_flatten, ← Array.map_reverse, Array.findSome?_map, Function.comp_def]
  rfl

theorem back?_mkVector (a : α) (n : Nat) :
    (mkVector n a).back? = if n = 0 then none else some a := by
  rw [mkVector_eq_mk_mkArray]
  simp only [back?_mk, Array.back?_mkArray]

@[simp] theorem back_mkArray [NeZero n] : (mkVector n a).back = a := by
  simp [back_eq_getElem]

/-! ### leftpad and rightpad -/

@[simp] theorem leftpad_mk (n : Nat) (a : α) (xs : Array α) (h : xs.size = m) :
    (Vector.mk xs h).leftpad n a = Vector.mk (Array.leftpad n a xs) (by simp [h]; omega) := by
  simp [h]

@[simp] theorem rightpad_mk (n : Nat) (a : α) (xs : Array α) (h : xs.size = m) :
    (Vector.mk xs h).rightpad n a = Vector.mk (Array.rightpad n a xs) (by simp [h]; omega) := by
  simp [h]

/-! ### contains -/

theorem contains_eq_any_beq [BEq α] (xs : Vector α n) (a : α) : xs.contains a = xs.any (a == ·) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.contains_eq_any_beq]

theorem contains_iff_exists_mem_beq [BEq α] {xs : Vector α n} {a : α} :
    xs.contains a ↔ ∃ a' ∈ xs, a == a' := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.contains_iff_exists_mem_beq]

theorem contains_iff_mem [BEq α] [LawfulBEq α] {xs : Vector α n} {a : α} :
    xs.contains a ↔ a ∈ xs := by
  simp

/-! ### more lemmas about `pop` -/

@[simp] theorem pop_empty : (#v[] : Vector α 0).pop = #v[] := rfl

@[simp] theorem pop_push (xs : Vector α n) : (xs.push x).pop = xs := by simp [pop]

@[simp] theorem getElem_pop {xs : Vector α n} {i : Nat} (h : i < n - 1) :
    xs.pop[i] = xs[i] := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem getElem?_pop (xs : Vector α n) (i : Nat) :
    xs.pop[i]? = if i < n - 1 then xs[i]? else none := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem?_pop]

theorem back_pop {xs : Vector α n} [h : NeZero (n - 1)] :
   xs.pop.back =
     xs[n - 2]'(by have := h.out; omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.back_pop]

theorem back?_pop {xs : Vector α n} :
    xs.pop.back? = if n ≤ 1 then none else xs[n - 2]? := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.back?_pop]

@[simp] theorem pop_append_of_size_ne_zero {xs : Vector α n} {ys : Vector α m} (h : m ≠ 0) :
    (xs ++ ys).pop = (xs ++ ys.pop).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [mk_append_mk, pop_mk, cast_mk, eq_mk]
  rw [Array.pop_append_of_ne_empty]
  apply Array.ne_empty_of_size_pos
  omega

theorem pop_append {xs : Vector α n} {ys : Vector α m} :
    (xs ++ ys).pop = if h : m = 0 then xs.pop.cast (by omega) else (xs ++ ys.pop).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [mk_append_mk, pop_mk, List.length_eq_zero_iff, Array.toList_eq_nil_iff, cast_mk, mk_eq]
  rw [Array.pop_append]
  split <;> simp_all

@[simp] theorem pop_mkVector (n) (a : α) : (mkVector n a).pop = mkVector (n - 1) a := by
  ext <;> simp

/-! Content below this point has not yet been aligned with `List` and `Array`. -/

set_option linter.indexVariables false in
@[simp] theorem getElem_push_last {xs : Vector α n} {x : α} : (xs.push x)[n] = x := by
  rcases xs with ⟨xs, rfl⟩
  simp

/--
Variant of `getElem_pop` that will sometimes fire when `getElem_pop` gets stuck because of
defeq issues in the implicit size argument.
-/
@[simp] theorem getElem_pop' (xs : Vector α (n + 1)) (i : Nat) (h : i < n + 1 - 1) :
    @getElem (Vector α n) Nat α (fun _ i => i < n) instGetElemNatLt xs.pop i h = xs[i] :=
  getElem_pop h

@[simp] theorem push_pop_back (xs : Vector α (n + 1)) : xs.pop.push xs.back = xs := by
  ext i
  by_cases h : i < n
  · simp [h]
  · replace h : i = xs.size - 1 := by rw [size_toArray]; omega
    subst h
    simp [back]

/-! ### findRev? and findSomeRev? -/

@[simp] theorem findRev?_eq_find?_reverse (f : α → Bool) (xs : Vector α n) :
    findRev? f xs = find? f xs.reverse := by
  simp [findRev?, find?]

@[simp] theorem findSomeRev?_eq_findSome?_reverse (f : α → Option β) (xs : Vector α n) :
    findSomeRev? f xs = findSome? f xs.reverse := by
  simp [findSomeRev?, findSome?]

/-! ### zipWith -/

@[simp] theorem getElem_zipWith (f : α → β → γ) (as : Vector α n) (bs : Vector β n) (i : Nat)
    (hi : i < n) : (zipWith f as bs)[i] = f as[i] bs[i] := by
  cases as
  cases bs
  simp

/-! ### take -/

set_option linter.indexVariables false in
@[simp] theorem take_size (as : Vector α n) : as.take n = as.cast (by simp) := by
  rcases as with ⟨as, rfl⟩
  simp

/-! ### swap -/

theorem getElem_swap (xs : Vector α n) (i j : Nat) {hi hj} (k : Nat) (hk : k < n) :
    (xs.swap i j hi hj)[k] = if k = i then xs[j] else if k = j then xs[i] else xs[k] := by
  cases xs
  simp_all [Array.getElem_swap]

@[simp] theorem getElem_swap_right (xs : Vector α n) {i j : Nat} {hi hj} :
    (xs.swap i j hi hj)[j]'(by simpa using hj) = xs[i] := by
  simp +contextual [getElem_swap]

@[simp] theorem getElem_swap_left (xs : Vector α n) {i j : Nat} {hi hj} :
    (xs.swap i j hi hj)[i]'(by simpa using hi) = xs[j] := by
  simp [getElem_swap]

@[simp] theorem getElem_swap_of_ne (xs : Vector α n) {i j : Nat} {hi hj} (hk : k < n)
      (hi' : k ≠ i) (hj' : k ≠ j) : (xs.swap i j hi hj)[k] = xs[k] := by
  simp_all [getElem_swap]

@[simp] theorem swap_swap (xs : Vector α n) {i j : Nat} {hi hj} :
    (xs.swap i j hi hj).swap i j hi hj = xs := by
  cases xs
  simp_all [Array.swap_swap]

theorem swap_comm (xs : Vector α n) {i j : Nat} {hi hj} :
    xs.swap i j hi hj = xs.swap j i hj hi := by
  cases xs
  simp only [swap_mk, mk.injEq]
  rw [Array.swap_comm]

/-! ### range -/

@[simp] theorem getElem_range (i : Nat) (hi : i < n) : (Vector.range n)[i] = i := by
  simp [Vector.range]

/-! ### take -/

@[simp] theorem getElem_take (xs : Vector α n) (j : Nat) (hi : i < min n j) :
    (xs.take j)[i] = xs[i] := by
  cases xs
  simp

/-! ### drop -/

@[simp] theorem getElem_drop (xs : Vector α n) (j : Nat) (hi : i < n - j) :
    (xs.drop j)[i] = xs[j + i] := by
  cases xs
  simp

/-! ### Decidable quantifiers. -/

theorem forall_zero_iff {P : Vector α 0 → Prop} :
    (∀ xs, P xs) ↔ P #v[] := by
  constructor
  · intro h
    apply h
  · intro h xs
    obtain (rfl : xs = #v[]) := (by ext i h; simp at h)
    apply h

theorem forall_cons_iff {P : Vector α (n + 1) → Prop} :
    (∀ xs : Vector α (n + 1), P xs) ↔ (∀ (x : α) (xs : Vector α n), P (xs.push x)) := by
  constructor
  · intro h _ _
    apply h
  · intro h xs
    have w : xs = xs.pop.push xs.back := by simp
    rw [w]
    apply h

instance instDecidableForallVectorZero (P : Vector α 0 → Prop) :
    ∀ [Decidable (P #v[])], Decidable (∀ xs, P xs)
  | .isTrue h => .isTrue fun ⟨xs, s⟩ => by
    obtain (rfl : xs = .empty) := (by ext i h₁ h₂; exact s; cases h₂)
    exact h
  | .isFalse h => .isFalse (fun w => h (w _))

instance instDecidableForallVectorSucc (P : Vector α (n+1) → Prop)
    [Decidable (∀ (x : α) (xs : Vector α n), P (xs.push x))] : Decidable (∀ xs, P xs) :=
  decidable_of_iff' (∀ x (xs : Vector α n), P (xs.push x)) forall_cons_iff

instance instDecidableExistsVectorZero (P : Vector α 0 → Prop) [Decidable (P #v[])] :
    Decidable (∃ xs, P xs) :=
  decidable_of_iff (¬ ∀ xs, ¬ P xs) Classical.not_forall_not

instance instDecidableExistsVectorSucc (P : Vector α (n+1) → Prop)
    [Decidable (∀ (x : α) (xs : Vector α n), ¬ P (xs.push x))] : Decidable (∃ xs, P xs) :=
  decidable_of_iff (¬ ∀ xs, ¬ P xs) Classical.not_forall_not
