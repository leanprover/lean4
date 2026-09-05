/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.BitVec.Lemmas
public import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.BitVec.Bootstrap
import Init.Data.List.TakeDrop
import Init.Data.List.Nat.TakeDrop
import Init.Data.Array.Lemmas
import Init.Data.Array.Bootstrap
import Init.ByCases
import Init.Omega


/-!
## Tail-recursive implementations for `BitVec` definitions.

The reference definitions in `Init.Data.BitVec.Basic` (e.g. `BitVec.ofBoolListLE`) are
clean for proofs but not tail-recursive, and stack-overflow on lists with ~1M elements.
This file provides asymptotically faster, non-stack-using implementations selected at
runtime via `@[csimp]`.

The strategy is to pack bits in 64-bit chunks (`packChunk`, `collectChunks`) and combine
the chunks with a balanced tree merge (`mergePass`, `treeMerge`), giving O(n log n) work
and O(1) stack usage. Correctness goes through the list-level spec function `flattenList`,
which gives the intended `Nat` semantics of a list of `(value, width)` pairs. Every step
is an unconditional `Nat` identity, so no well-formedness invariant is needed.
-/

namespace BitVec.Internal

/-! ### Definitions -/

/--
Pack the next up-to-`remaining` bools (LSB-first) into `chunk`, starting at bit index `used`.
-/
def packChunk : List Bool → Nat → Nat → Nat → Nat × Nat × List Bool
  | [],      _,   chunk, used => (chunk, used, [])
  | bs,      0,   chunk, used => (chunk, used, bs)
  | b :: bs, k+1, chunk, used =>
    let chunk' := if b then chunk ||| (1 <<< used) else chunk
    packChunk bs k chunk' (used + 1)

/-- Walk a list of `Bool`s in 64-bit chunks, producing `(value, width)` pairs. -/
def collectChunks : Nat → List Bool → Array (Nat × Nat) → Array (Nat × Nat)
  | _,   [],      acc => acc
  | 0,   _,       acc => acc -- unreachable when fuel ≥ list length
  | n+1, b :: bs, acc =>
    let (chunk, used, rest) := packChunk (b :: bs) 64 0 0
    collectChunks n rest (acc.push (chunk, used))

/-- One pass of a balanced binary merge. -/
def mergePass (arr : Array (Nat × Nat)) : Array (Nat × Nat) :=
  go 0 (Array.mkEmpty ((arr.size + 1) / 2))
where
  go (i : Nat) (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
    if h : i + 1 < arr.size then
      let (lo, lb) := arr[i]'(Nat.lt_of_succ_lt h)
      let (hi, hb) := arr[i+1]
      go (i + 2) (acc.push (lo ||| (hi <<< lb), lb + hb))
    else if h : i < arr.size then
      acc.push arr[i]
    else
      acc
  termination_by arr.size - i
  decreasing_by
    simp_wf
    exact Nat.lt_trans (Nat.sub_succ_lt_self arr.size (i+1) h)
            (Nat.sub_succ_lt_self arr.size i (Nat.lt_of_succ_lt h))

/-- Tree-merge with explicit fuel. -/
def treeMerge (arr : Array (Nat × Nat)) : Nat :=
  go arr.size arr
where
  go : Nat → Array (Nat × Nat) → Nat
  | 0,    arr => if h : 0 < arr.size then arr[0].1 else 0
  | n+1,  arr =>
    if h : arr.size ≤ 1 then
      if h0 : 0 < arr.size then arr[0].1 else 0
    else
      go n (mergePass arr)

/-- A single bit becomes a width-1 `(value, width)` leaf. -/
def leaf (b : Bool) : Nat × Nat := (b.toNat, 1)

/-- Tail-recursive implementation of `BitVec.ofBoolListLE`. -/
public def ofBoolListLEImpl (bs : List Bool) : BitVec bs.length :=
  BitVec.ofNat bs.length
    (treeMerge (collectChunks bs.length bs (Array.mkEmpty ((bs.length + 63) / 64))))

/-- Tail-recursive implementation of `BitVec.ofBoolListBE`: reverse, then LE. -/
public def ofBoolListBEImpl (bs : List Bool) : BitVec bs.length :=
  (ofBoolListLEImpl bs.reverse).cast List.length_reverse

/-! ### Helpers -/

/-- If `a ≤ 2^(k+1)` then `(a + 1) / 2 ≤ 2^k`. Used for the `mergePass` halving step. -/
theorem half_le_pow_of_le_double {a k : Nat} (h : a ≤ 2^(k+1)) :
    (a + 1) / 2 ≤ 2^k := by
  rw [Nat.two_pow_succ] at h
  generalize 2^k = m at *
  omega

/-! ### flattenList spec function -/

/-- The `Nat` denoted by a list of `(value, width)` pairs: concatenate the bit-fields. -/
def flattenList : List (Nat × Nat) → Nat
  | [] => 0
  | (v, w) :: rest => v ||| (flattenList rest <<< w)

/-- The total bit-width of a list of `(value, width)` pairs. -/
def totalWidth : List (Nat × Nat) → Nat
  | [] => 0
  | (_, w) :: rest => w + totalWidth rest

theorem totalWidth_append (xs ys : List (Nat × Nat)) :
    totalWidth (xs ++ ys) = totalWidth xs + totalWidth ys := by
  induction xs with
  | nil => simp [totalWidth]
  | cons p rest ih =>
    obtain ⟨v, w⟩ := p
    simp only [List.cons_append, totalWidth]; omega

theorem flattenList_append (xs ys : List (Nat × Nat)) :
    flattenList (xs ++ ys) = flattenList xs ||| (flattenList ys <<< totalWidth xs) := by
  induction xs with
  | nil => simp [flattenList, totalWidth]
  | cons p rest ih =>
    obtain ⟨v, w⟩ := p
    simp only [List.cons_append, flattenList, totalWidth]
    rw [ih, Nat.shiftLeft_or_distrib, ← Nat.or_assoc]
    rw [show flattenList ys <<< totalWidth rest <<< w
         = flattenList ys <<< (w + totalWidth rest) from by
      rw [← Nat.shiftLeft_add]; congr 1; omega]

theorem flattenList_singleton (v w : Nat) : flattenList [(v, w)] = v := by
  simp [flattenList]

/-! ### List-level mergePass -/

/-- The list-level specification of one `mergePass`. -/
def mergePassList : List (Nat × Nat) → List (Nat × Nat)
  | (lo, lb) :: (hi, hb) :: rest =>
    (lo ||| (hi <<< lb), lb + hb) :: mergePassList rest
  | rest => rest

theorem mergePassList_length (xs : List (Nat × Nat)) :
    (mergePassList xs).length = (xs.length + 1) / 2 := by
  match xs with
  | [] => rfl
  | [_] => simp [mergePassList]
  | (lo, lb) :: (hi, hb) :: rest =>
    simp only [mergePassList, List.length_cons]
    rw [mergePassList_length rest]; omega

/-- Merging two adjacent fields is associativity of `|||` after distributing `<<<`. -/
theorem flattenList_pack (lo lb hi hb : Nat) (rest : List (Nat × Nat)) :
    (lo ||| (hi <<< lb)) ||| (flattenList rest <<< (lb + hb))
      = lo ||| ((hi ||| (flattenList rest <<< hb)) <<< lb) := by
  rw [Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.add_comm hb lb, Nat.or_assoc]

theorem flattenList_mergePassList : ∀ (xs : List (Nat × Nat)),
    flattenList (mergePassList xs) = flattenList xs
  | [] => rfl
  | [_] => rfl
  | (lo, lb) :: (hi, hb) :: rest => by
    simp only [mergePassList, flattenList]
    rw [flattenList_mergePassList rest]
    exact flattenList_pack lo lb hi hb rest

/-! ### Relate Array `mergePass` to List `mergePassList` -/

theorem mergePass_go_toList_aux (arr : Array (Nat × Nat)) :
    ∀ (n i : Nat) (acc : Array (Nat × Nat)), arr.size - i ≤ n →
    (mergePass.go arr i acc).toList = acc.toList ++ mergePassList (arr.toList.drop i) := by
  intro n
  induction n with
  | zero =>
    intro i acc hbound
    have hge : arr.size ≤ i := by omega
    rw [mergePass.go]
    have hi_neg : ¬ i + 1 < arr.size := by omega
    have hi_neg2 : ¬ i < arr.size := by omega
    simp only [hi_neg, ↓reduceDIte, hi_neg2, ↓reduceDIte]
    have hdrop : arr.toList.drop i = [] :=
      List.drop_of_length_le (by simpa using hge)
    simp [hdrop, mergePassList]
  | succ k ih =>
    intro i acc hbound
    rw [mergePass.go]
    by_cases h1 : i + 1 < arr.size
    · simp only [h1, ↓reduceDIte]
      have hi_lt : i < arr.size := Nat.lt_of_succ_lt h1
      have hbk : arr.size - (i + 2) ≤ k := by omega
      have hdrop : arr.toList.drop i = arr[i] :: arr[i+1] :: arr.toList.drop (i+2) := by
        have h_step1 : arr.toList.drop i
                     = arr.toList[i] :: arr.toList.drop (i+1) :=
          List.drop_eq_getElem_cons (by simpa using hi_lt)
        have h_step2 : arr.toList.drop (i+1)
                     = arr.toList[i+1] :: arr.toList.drop (i+1+1) :=
          List.drop_eq_getElem_cons (by simpa using h1)
        rw [h_step1, h_step2]
        simp [show i + 1 + 1 = i + 2 from by omega]
      rw [hdrop]
      rw [ih (i+2) _ hbk]
      simp only [mergePassList, Array.toList_push, List.append_assoc, List.cons_append,
        List.nil_append]
    · simp only [h1, ↓reduceDIte]
      by_cases h2 : i < arr.size
      · simp only [h2, ↓reduceDIte]
        have hge : i + 1 ≥ arr.size := Nat.le_of_not_lt h1
        have hdrop : arr.toList.drop i = [arr[i]] := by
          have h_step1 : arr.toList.drop i
                       = arr.toList[i] :: arr.toList.drop (i+1) :=
            List.drop_eq_getElem_cons (by simpa using h2)
          have h_step2 : arr.toList.drop (i+1) = [] :=
            List.drop_of_length_le (by simp; omega)
          rw [h_step1, h_step2]
          simp
        rw [hdrop, Array.toList_push]
        simp [mergePassList]
      · simp only [h2, ↓reduceDIte]
        have hdrop : arr.toList.drop i = [] :=
          List.drop_of_length_le (by simpa using Nat.le_of_not_lt h2)
        simp [hdrop, mergePassList]

theorem mergePass_go_toList (arr : Array (Nat × Nat)) (i : Nat) (acc : Array (Nat × Nat)) :
    (mergePass.go arr i acc).toList = acc.toList ++ mergePassList (arr.toList.drop i) :=
  mergePass_go_toList_aux arr (arr.size - i) i acc (Nat.le_refl _)

theorem mergePass_toList (arr : Array (Nat × Nat)) :
    (mergePass arr).toList = mergePassList arr.toList := by
  unfold mergePass
  rw [mergePass_go_toList]
  simp [Array.mkEmpty_eq]

theorem mergePass_size (arr : Array (Nat × Nat)) :
    (mergePass arr).size = (arr.size + 1) / 2 := by
  simpa [mergePassList_length] using congrArg List.length (mergePass_toList arr)

/-! ### treeMerge correctness -/

theorem toList_size_one {arr : Array (Nat × Nat)} (h : arr.size = 1) :
    arr.toList = [arr[0]] := by
  obtain ⟨p, rfl⟩ := Array.size_eq_one_iff.mp h
  rfl

theorem toList_size_zero {arr : Array (Nat × Nat)} (h : arr.size = 0) :
    arr.toList = [] :=
  List.length_eq_zero_iff.mp (by simp [h])

theorem treeMerge_go_eq_flattenList (n : Nat) (arr : Array (Nat × Nat))
    (hsize : arr.size ≤ 2^n) :
    treeMerge.go n arr = flattenList arr.toList := by
  induction n generalizing arr with
  | zero =>
    have hsz : arr.size ≤ 1 := by simpa using hsize
    rw [treeMerge.go]
    by_cases h0 : 0 < arr.size
    · simp only [h0, ↓reduceDIte]
      have hsize1 : arr.size = 1 := by omega
      rw [toList_size_one hsize1]
      simp [flattenList]
    · simp only [h0, ↓reduceDIte]
      rw [toList_size_zero (by omega)]; rfl
  | succ k ih =>
    rw [treeMerge.go]
    by_cases hle : arr.size ≤ 1
    · simp only [hle, ↓reduceDIte]
      by_cases h0 : 0 < arr.size
      · simp only [h0, ↓reduceDIte]
        have hsize1 : arr.size = 1 := by clear hsize; omega
        rw [toList_size_one hsize1]
        simp [flattenList]
      · simp only [h0, ↓reduceDIte]
        have h0z : arr.size = 0 := by clear hsize; omega
        rw [toList_size_zero h0z]; rfl
    · simp only [hle, ↓reduceDIte]
      have hsize' : (mergePass arr).size ≤ 2^k := by
        rw [mergePass_size]; exact half_le_pow_of_le_double hsize
      rw [ih _ hsize', mergePass_toList]
      exact flattenList_mergePassList arr.toList

theorem treeMerge_eq_flattenList (arr : Array (Nat × Nat)) :
    treeMerge arr = flattenList arr.toList := by
  unfold treeMerge
  exact treeMerge_go_eq_flattenList _ _ (Nat.le_of_lt Nat.lt_two_pow_self)

/-! ### Leaf list correctness -/

theorem totalWidth_map_leaf (bs : List Bool) : totalWidth (bs.map leaf) = bs.length := by
  induction bs <;> simp [totalWidth, leaf, *] <;> omega

theorem testBit_flattenList_leaves (bs : List Bool) (i : Nat) :
    (flattenList (bs.map leaf)).testBit i = bs.getD i false := by
  induction bs generalizing i with
  | nil => simp [flattenList]
  | cons b bs ih =>
    simp only [List.map_cons, flattenList, leaf, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => cases b <;> simp
    | succ j =>
      have hb : b.toNat.testBit (j+1) = false := by cases b <;> simp [Nat.testBit_succ]
      rw [Nat.add_sub_cancel, ih, hb]
      simp

/-! ### packChunk correctness -/

theorem packChunk_used (bs : List Bool) (r c u : Nat) :
    (packChunk bs r c u).2.1 = u + (bs.take r).length := by
  induction bs generalizing r c u with
  | nil => simp [packChunk]
  | cons b bs ih =>
    cases r <;> simp [packChunk, ih] <;> omega

theorem packChunk_rest (bs : List Bool) (r c u : Nat) :
    (packChunk bs r c u).2.2 = bs.drop r := by
  induction bs generalizing r c u with
  | nil => simp [packChunk]
  | cons b bs ih =>
    cases r <;> simp [packChunk, ih]

/-- The chunk value built by `packChunk` is the `flattenList` of the consumed bits as leaves,
shifted into place above `used`. -/
theorem packChunk_eq (bs : List Bool) (r c u : Nat) :
    (packChunk bs r c u).1 = c ||| (flattenList ((bs.take r).map leaf) <<< u) := by
  induction bs generalizing r c u with
  | nil => simp [packChunk, flattenList]
  | cons b bs ih =>
    cases r with
    | zero => simp [packChunk, flattenList]
    | succ r =>
      simp only [packChunk, List.take_succ_cons, List.map_cons, flattenList, leaf]
      rw [ih]
      have hstep : (if b then c ||| (1 <<< u) else c) = c ||| (b.toNat <<< u) := by
        cases b <;> simp
      rw [hstep, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.add_comm 1 u, Nat.or_assoc]

/-! ### collectChunks correctness -/

/-- The `flattenList` value of the chunks produced by `collectChunks`. -/
theorem flattenList_collectChunks (fuel : Nat) (bs : List Bool) (acc : Array (Nat × Nat))
    (hfuel : bs.length ≤ 64 * fuel) :
    flattenList (collectChunks fuel bs acc).toList
      = flattenList acc.toList ||| (flattenList (bs.map leaf) <<< totalWidth acc.toList) := by
  induction fuel generalizing bs acc with
  | zero =>
    have hbs : bs = [] := List.length_eq_zero_iff.mp (by omega)
    subst hbs
    simp [collectChunks, flattenList]
  | succ k ih =>
    cases bs with
    | nil => simp [collectChunks, flattenList]
    | cons b bs =>
      have hchunk : (packChunk (b :: bs) 64 0 0).1
          = flattenList (((b :: bs).take 64).map leaf) := by
        rw [packChunk_eq]; simp
      have hused : (packChunk (b :: bs) 64 0 0).2.1 = ((b :: bs).take 64).length := by
        simp [packChunk_used]
      have hrest : (packChunk (b :: bs) 64 0 0).2.2 = (b :: bs).drop 64 :=
        packChunk_rest (b :: bs) 64 0 0
      have hrest_len : ((b :: bs).drop 64).length ≤ 64 * k := by
        rw [List.length_drop]
        simp only [List.length_cons] at hfuel ⊢
        omega
      -- unfold one step, rewrite the chunk pieces, and apply the inductive hypothesis
      simp only [collectChunks]
      rw [hchunk, hused, hrest, ih ((b :: bs).drop 64) _ hrest_len]
      rw [Array.toList_push, flattenList_append, flattenList_singleton, totalWidth_append]
      simp only [totalWidth, Nat.add_zero]
      -- split the bit list into its first 64 bits and the rest
      have hsplit : (b :: bs).map leaf
          = ((b :: bs).take 64).map leaf ++ ((b :: bs).drop 64).map leaf := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit, flattenList_append, totalWidth_map_leaf]
      exact flattenList_pack (flattenList acc.toList) (totalWidth acc.toList)
        (flattenList (((b :: bs).take 64).map leaf)) ((b :: bs).take 64).length
        (((b :: bs).drop 64).map leaf)

/-! ### Main correctness theorems -/

theorem getLsbD_ofBoolListLEImpl (bs : List Bool) (i : Nat) (hi : i < bs.length) :
    (ofBoolListLEImpl bs).getLsbD i = bs.getD i false := by
  unfold ofBoolListLEImpl
  rw [getLsbD_ofNat]
  simp only [hi, decide_true, Bool.true_and]
  rw [treeMerge_eq_flattenList, flattenList_collectChunks _ _ _ (by omega)]
  simp [Array.mkEmpty_eq, flattenList, totalWidth, testBit_flattenList_leaves]

theorem getLsbD_ofBoolListBEImpl (bs : List Bool) (i : Nat) (hi : i < bs.length) :
    (ofBoolListBEImpl bs).getLsbD i =
      (decide (i < bs.length) && bs.getD (bs.length - 1 - i) false) := by
  unfold ofBoolListBEImpl
  rw [BitVec.getLsbD_cast]
  have hi' : i < bs.reverse.length := by simpa using hi
  rw [getLsbD_ofBoolListLEImpl bs.reverse i hi']
  simp only [hi, decide_true, Bool.true_and]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_reverse hi]

/-! ### General `BitVec n` chunked collect (for `BitVec.flattenList`) -/

/--
A `BitVec n` becomes a width-`n` `(value, width)` leaf. This is the general-width
analogue of `leaf`, reusing the same `Array (Nat × Nat)` merge core (`mergePass`,
`treeMerge`) as the `ofBoolListLE` path.
-/
def bvLeaf {n : Nat} (x : BitVec n) : Nat × Nat := (x.toNat, n)

/--
Pack up to `remaining` width-`n` bitvectors (LSB-first) into `chunk`, starting at bit `used`.
-/
def packChunkBV {n : Nat} :
    List (BitVec n) → Nat → Nat → Nat → Nat × Nat × List (BitVec n)
  | [],      _,   chunk, used => (chunk, used, [])
  | xs,      0,   chunk, used => (chunk, used, xs)
  | x :: xs, k+1, chunk, used =>
    packChunkBV xs k (chunk ||| (x.toNat <<< used)) (used + n)

/-- Walk a `List (BitVec n)` in chunks of `cap` elements, producing `(value, width)` pairs. -/
def collectChunksBV {n : Nat} (cap : Nat) :
    Nat → List (BitVec n) → Array (Nat × Nat) → Array (Nat × Nat)
  | _,   [],      acc => acc
  | 0,   _,       acc => acc -- unreachable when fuel ≥ list length
  | f+1, x :: xs, acc =>
    let (chunk, used, rest) := packChunkBV (x :: xs) cap 0 0
    collectChunksBV cap f rest (acc.push (chunk, used))

theorem totalWidth_map_bvLeaf {n : Nat} (xs : List (BitVec n)) :
    totalWidth (xs.map bvLeaf) = n * xs.length := by
  induction xs with
  | nil => simp [totalWidth]
  | cons x xs ih =>
    simp only [List.map_cons, totalWidth, bvLeaf, List.length_cons, ih, Nat.mul_succ]
    omega

theorem packChunkBV_used {n : Nat} (xs : List (BitVec n)) (r c u : Nat) :
    (packChunkBV xs r c u).2.1 = u + n * (xs.take r).length := by
  induction xs generalizing r c u with
  | nil => simp [packChunkBV]
  | cons x xs ih =>
    cases r with
    | zero => simp [packChunkBV]
    | succ r =>
      simp only [packChunkBV, ih, List.take_succ_cons, List.length_cons, Nat.mul_succ]
      omega

theorem packChunkBV_rest {n : Nat} (xs : List (BitVec n)) (r c u : Nat) :
    (packChunkBV xs r c u).2.2 = xs.drop r := by
  induction xs generalizing r c u with
  | nil => simp [packChunkBV]
  | cons x xs ih =>
    cases r <;> simp [packChunkBV, ih]

theorem packChunkBV_eq {n : Nat} (xs : List (BitVec n)) (r c u : Nat) :
    (packChunkBV xs r c u).1 = c ||| (flattenList ((xs.take r).map bvLeaf) <<< u) := by
  induction xs generalizing r c u with
  | nil => simp [packChunkBV, flattenList]
  | cons x xs ih =>
    cases r with
    | zero => simp [packChunkBV, flattenList]
    | succ r =>
      simp only [packChunkBV, List.take_succ_cons, List.map_cons, flattenList, bvLeaf]
      rw [ih]
      rw [Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.add_comm n u, Nat.or_assoc]

/-- The `flattenList` value of the chunks produced by `collectChunksBV`. -/
theorem flattenList_collectChunksBV {n : Nat} (cap : Nat)
    (fuel : Nat) (xs : List (BitVec n)) (acc : Array (Nat × Nat))
    (hfuel : xs.length ≤ cap * fuel) :
    flattenList (collectChunksBV cap fuel xs acc).toList
      = flattenList acc.toList ||| (flattenList (xs.map bvLeaf) <<< totalWidth acc.toList) := by
  induction fuel generalizing xs acc with
  | zero =>
    have hxs : xs = [] := List.length_eq_zero_iff.mp (by simpa using hfuel)
    subst hxs
    simp [collectChunksBV, flattenList]
  | succ k ih =>
    cases xs with
    | nil => simp [collectChunksBV, flattenList]
    | cons x xs =>
      have hchunk : (packChunkBV (x :: xs) cap 0 0).1
          = flattenList (((x :: xs).take cap).map bvLeaf) := by
        rw [packChunkBV_eq]; simp
      have hused : (packChunkBV (x :: xs) cap 0 0).2.1
          = totalWidth (((x :: xs).take cap).map bvLeaf) := by
        rw [packChunkBV_used, totalWidth_map_bvLeaf]; simp
      have hrest : (packChunkBV (x :: xs) cap 0 0).2.2 = (x :: xs).drop cap :=
        packChunkBV_rest (x :: xs) cap 0 0
      have hrest_len : ((x :: xs).drop cap).length ≤ cap * k := by
        rw [List.length_drop]
        have hbnd : (x :: xs).length ≤ cap * k + cap := by
          rw [← Nat.mul_succ]; exact hfuel
        omega
      simp only [collectChunksBV]
      rw [hchunk, hused, hrest, ih ((x :: xs).drop cap) _ hrest_len]
      rw [Array.toList_push, flattenList_append, flattenList_singleton, totalWidth_append]
      simp only [totalWidth, Nat.add_zero]
      have hsplit : (x :: xs).map bvLeaf
          = ((x :: xs).take cap).map bvLeaf ++ ((x :: xs).drop cap).map bvLeaf := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit, flattenList_append]
      exact flattenList_pack (flattenList acc.toList) (totalWidth acc.toList)
        (flattenList (((x :: xs).take cap).map bvLeaf))
        (totalWidth (((x :: xs).take cap).map bvLeaf))
        (((x :: xs).drop cap).map bvLeaf)

/-- Bridge: the `Nat`-level `flattenList` of the reversed leaves is `BitVec.flattenList`.
The reverse mirrors `ofBoolListBEImpl`: `BitVec.flattenList` places the list head in the
high bits, whereas the `Nat × Nat` `flattenList` places it in the low bits. -/
theorem toNat_flattenList_eq {n : Nat} (xs : List (BitVec n)) :
    (BitVec.flattenList xs).toNat = flattenList (xs.reverse.map bvLeaf) := by
  induction xs with
  | nil => simp [BitVec.flattenList, flattenList]
  | cons x xs ih =>
    rw [show x :: xs = [x] ++ xs from rfl, BitVec.toNat_flattenList_append, ih]
    have hx : (BitVec.flattenList [x]).toNat = x.toNat := by
      simp [BitVec.flattenList]
    rw [hx]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.map_append, List.map_cons, List.map_nil, flattenList_append, flattenList_singleton,
      bvLeaf, totalWidth_map_bvLeaf, List.length_reverse]
    rw [Nat.or_comm]

/-- Number of width-`n` elements that fit into one ~64-bit machine word (at least one). -/
def chunkCap (n : Nat) : Nat := max 1 (64 / n)

theorem chunkCap_pos (n : Nat) : 0 < chunkCap n := by
  unfold chunkCap
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (64 / n))

/--
Chunked, `O(1)`-stack implementation of `BitVec.flattenList`, sharing the `Array (Nat × Nat)`
merge core (`mergePass`, `treeMerge`) with `ofBoolListLEImpl`. Packs `chunkCap n` width-`n`
values per ~64-bit chunk, then tree-merges, giving `O(n * L * log L)` work and `O(1)` stack
(versus an `O(log L)`-stack divide-and-conquer worker that re-slices the list with
`take`/`drop` at every node).

`BitVec.flattenList` places the list head in the high bits, so the leaves are collected from
`xs.reverse` (one up-front `O(L)` traversal/allocation), matching `ofBoolListBEImpl`.
The `Array.mkEmpty` argument is only a capacity hint; it does not affect the result.
-/
public def flattenListImpl {n : Nat} (xs : List (BitVec n)) : BitVec (n * xs.length) :=
  let cap := chunkCap n
  let len := xs.length
  BitVec.ofNat (n * len)
    (treeMerge (collectChunksBV cap len xs.reverse (Array.mkEmpty ((len + cap - 1) / cap))))

theorem flattenListImpl_eq {n : Nat} (xs : List (BitVec n)) :
    flattenListImpl xs = BitVec.flattenList xs := by
  have hlen : xs.reverse.length ≤ chunkCap n * xs.length := by
    rw [List.length_reverse]
    calc xs.length = 1 * xs.length := by rw [Nat.one_mul]
      _ ≤ chunkCap n * xs.length := Nat.mul_le_mul_right _ (chunkCap_pos n)
  have hval : treeMerge (collectChunksBV (chunkCap n) xs.length xs.reverse
      (Array.mkEmpty ((xs.length + chunkCap n - 1) / chunkCap n)))
      = (BitVec.flattenList xs).toNat := by
    rw [treeMerge_eq_flattenList,
      flattenList_collectChunksBV (chunkCap n) xs.length xs.reverse _ hlen]
    simp [Array.mkEmpty_eq, flattenList, totalWidth, toNat_flattenList_eq]
  simp only [flattenListImpl]
  rw [hval]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]

end BitVec.Internal

namespace BitVec

@[csimp]
public theorem ofBoolListLE_eq_impl : @ofBoolListLE = @BitVec.Internal.ofBoolListLEImpl := by
  funext bs
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBoolListLE]
  exact (BitVec.Internal.getLsbD_ofBoolListLEImpl bs i hi).symm

@[csimp]
public theorem ofBoolListBE_eq_impl : @ofBoolListBE = @BitVec.Internal.ofBoolListBEImpl := by
  funext bs
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBoolListBE]
  exact (BitVec.Internal.getLsbD_ofBoolListBEImpl bs i hi).symm

@[csimp]
public theorem flattenList_eq_impl : @BitVec.flattenList = @BitVec.Internal.flattenListImpl := by
  funext n xs
  exact (BitVec.Internal.flattenListImpl_eq xs).symm

end BitVec
