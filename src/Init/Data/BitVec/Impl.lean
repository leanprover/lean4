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
import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop
import Init.Data.List.Nat.TakeDrop
import Init.Data.Array.Lemmas
import Init.Data.Array.Bootstrap
import Init.Data.Nat.Lemmas
import Init.ByCases
import Init.Omega

public section

/-!
## Tail-recursive implementations for `BitVec` definitions.

The reference definitions in `Init.Data.BitVec.Basic` (e.g. `BitVec.ofBoolListLE`) are
clean for proofs but not tail-recursive, and stack-overflow on lists with ~1M elements.
This file provides asymptotically faster, non-stack-using implementations selected at
runtime via `@[csimp]`.
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

/-- Tail-recursive implementation of `BitVec.ofBoolListLE`. -/
def ofBoolListLEImpl (bs : List Bool) : BitVec bs.length :=
  let chunks := collectChunks bs.length bs (Array.mkEmpty ((bs.length + 63) / 64))
  BitVec.ofNat bs.length (treeMerge chunks)

/-- Tail-recursive implementation of `BitVec.ofBoolListBE`: reverse, then LE. -/
def ofBoolListBEImpl (bs : List Bool) : BitVec bs.length :=
  (ofBoolListLEImpl bs.reverse).cast List.length_reverse

/-! ### Helpers -/

private theorem two_pow_le_of_le {a b : Nat} (h : a ≤ b) : 2^a ≤ 2^b :=
  Nat.pow_le_pow_right (by decide) h

private theorem one_shiftLeft_lt_two_pow_succ (i : Nat) : (1 : Nat) <<< i < 2 ^ (i + 1) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.pow_lt_pow_succ (by decide)

private theorem step_lt (b : Bool) {c i : Nat} (h : c < 2^i) :
    (if b then c ||| (1 <<< i) else c) < 2^(i+1) := by
  cases b
  case false => exact Nat.lt_of_lt_of_le h (two_pow_le_of_le (Nat.le_succ i))
  case true =>
    apply Nat.or_lt_two_pow
    · exact Nat.lt_of_lt_of_le h (two_pow_le_of_le (Nat.le_succ i))
    · exact one_shiftLeft_lt_two_pow_succ i

private theorem testBit_step_at (b : Bool) {c i : Nat} (h : c < 2^i) :
    (if b then c ||| (1 <<< i) else c).testBit i = b := by
  have hci : c.testBit i = false := Nat.testBit_lt_two_pow h
  cases b
  case false => simp [hci]
  case true =>
    rw [if_pos rfl, Nat.testBit_or, Nat.testBit_shiftLeft]
    simp [hci]

private theorem testBit_step_lo (b : Bool) {c i j : Nat} (hji : j < i) :
    (if b then c ||| (1 <<< i) else c).testBit j = c.testBit j := by
  cases b
  case false => rfl
  case true =>
    rw [if_pos rfl, Nat.testBit_or, Nat.testBit_shiftLeft]
    have : ¬ i ≤ j := Nat.not_le_of_lt hji
    simp [this]

/-! ### packChunk invariants -/

private theorem packChunk_used (bs : List Bool) (r c u : Nat) :
    (packChunk bs r c u).2.1 = u + min bs.length r := by
  induction bs generalizing r c u with
  | nil => simp [packChunk]
  | cons b bs ih =>
    cases r with
    | zero => simp [packChunk]
    | succ r =>
      simp only [packChunk, List.length_cons]
      rw [ih]; omega

private theorem packChunk_rest (bs : List Bool) (r c u : Nat) :
    (packChunk bs r c u).2.2 = bs.drop (min bs.length r) := by
  induction bs generalizing r c u with
  | nil => simp [packChunk]
  | cons b bs ih =>
    cases r with
    | zero => simp [packChunk]
    | succ r =>
      simp only [packChunk, List.length_cons]
      rw [ih]
      have hmin : min (bs.length + 1) (r + 1) = min bs.length r + 1 := by omega
      rw [hmin]; rfl

private theorem packChunk_lt (bs : List Bool) (r c u : Nat) (h : c < 2^u) :
    (packChunk bs r c u).1 < 2^(u + min bs.length r) := by
  induction bs generalizing r c u with
  | nil => simpa [packChunk] using h
  | cons b bs ih =>
    cases r with
    | zero => simpa [packChunk] using h
    | succ r =>
      simp only [packChunk, List.length_cons]
      have hrw : u + 1 + min bs.length r = u + min (bs.length + 1) (r + 1) := by omega
      have step := step_lt b h
      have ih' := ih (r := r) (c := if b then c ||| (1 <<< u) else c) (u := u + 1) step
      rw [← hrw]; exact ih'

private theorem packChunk_testBit_lo (bs : List Bool) (r c u j : Nat) (hju : j < u) :
    (packChunk bs r c u).1.testBit j = c.testBit j := by
  induction bs generalizing r c u with
  | nil => simp [packChunk]
  | cons b bs ih =>
    cases r with
    | zero => simp [packChunk]
    | succ r =>
      simp only [packChunk]
      have hju1 : j < u + 1 := Nat.lt_succ_of_lt hju
      rw [ih (r := r) (c := if b then c ||| (1 <<< u) else c) (u := u + 1) hju1]
      exact testBit_step_lo b hju

private theorem packChunk_testBit_mid (bs : List Bool) (r c u j : Nat)
    (hc : c < 2^u) (hjr : j < min bs.length r) :
    (packChunk bs r c u).1.testBit (u + j) = bs.getD j false := by
  induction bs generalizing r c u j with
  | nil => simp at hjr
  | cons b bs ih =>
    cases r with
    | zero => simp at hjr
    | succ r =>
      simp only [packChunk]
      by_cases hj0 : j = 0
      · subst hj0
        simp only [Nat.add_zero, List.getD_cons_zero]
        rw [packChunk_testBit_lo bs r _ (u+1) u (Nat.lt_succ_self u)]
        exact testBit_step_at b hc
      · have hjm1 : j - 1 < min bs.length r := by
          simp only [List.length_cons] at hjr; omega
        have heq : u + 1 + (j - 1) = u + j := by omega
        have hcons : (b :: bs).getD j false = bs.getD (j - 1) false := by
          rw [show j = (j - 1) + 1 from by omega]
          exact List.getD_cons_succ
        have step := step_lt b hc
        have ih' := ih (r := r) (c := if b then c ||| (1 <<< u) else c) (u := u + 1)
          (j := j - 1) step hjm1
        rw [heq] at ih'
        rw [ih', hcons]

/-- The chunk produced from initial state `(c=0, u=0)` is well-formed. -/
private theorem packChunk_init_lt (bs : List Bool) (r : Nat) :
    (packChunk bs r 0 0).1 < 2^((packChunk bs r 0 0).2.1) := by
  rw [packChunk_used]
  exact packChunk_lt bs r 0 0 (by simp)

private theorem packChunk_init_testBit (bs : List Bool) (r j : Nat) (hjr : j < min bs.length r) :
    (packChunk bs r 0 0).1.testBit j = bs.getD j false := by
  have := packChunk_testBit_mid bs r 0 0 j (by simp) hjr
  simpa using this

/-! ### flattenList spec function -/

def flattenList : List (Nat × Nat) → Nat
  | [] => 0
  | (v, w) :: rest => v ||| (flattenList rest <<< w)

def totalWidth : List (Nat × Nat) → Nat
  | [] => 0
  | (_, w) :: rest => w + totalWidth rest

def WellFormedList (xs : List (Nat × Nat)) : Prop :=
  ∀ p ∈ xs, p.1 < 2^p.2

private theorem WellFormedList.nil : WellFormedList [] := by
  intro p hp; simp at hp

private theorem WellFormedList.tail {p : Nat × Nat} {rest : List (Nat × Nat)}
    (h : WellFormedList (p :: rest)) : WellFormedList rest :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

private theorem WellFormedList.head {p : Nat × Nat} {rest : List (Nat × Nat)}
    (h : WellFormedList (p :: rest)) : p.1 < 2^p.2 :=
  h p List.mem_cons_self

/-! ### Append lemmas -/

private theorem totalWidth_append (xs ys : List (Nat × Nat)) :
    totalWidth (xs ++ ys) = totalWidth xs + totalWidth ys := by
  induction xs with
  | nil => simp [totalWidth]
  | cons p rest ih =>
    obtain ⟨v, w⟩ := p
    simp only [List.cons_append, totalWidth]; omega

private theorem flattenList_append (xs ys : List (Nat × Nat)) :
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

private theorem flattenList_singleton (v w : Nat) : flattenList [(v, w)] = v := by
  simp [flattenList]

private theorem flattenList_lt (xs : List (Nat × Nat)) (h : WellFormedList xs) :
    flattenList xs < 2^(totalWidth xs) := by
  induction xs with
  | nil => simp [flattenList, totalWidth]
  | cons p rest ih =>
    obtain ⟨v, w⟩ := p
    simp only [flattenList, totalWidth]
    have hp : v < 2^w := h.head
    have hrest : WellFormedList rest := h.tail
    have ih' := ih hrest
    apply Nat.or_lt_two_pow
    · exact Nat.lt_of_lt_of_le hp (two_pow_le_of_le (Nat.le_add_right _ _))
    · rw [Nat.shiftLeft_eq]
      have hmul : flattenList rest * 2^w < 2^(totalWidth rest) * 2^w :=
        Nat.mul_lt_mul_of_pos_right ih' (Nat.two_pow_pos w)
      have heq : 2^(totalWidth rest) * 2^w = 2^(w + totalWidth rest) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [heq] at hmul; exact hmul

private theorem testBit_flattenList_high (xs : List (Nat × Nat)) (h : WellFormedList xs)
    (n : Nat) (hn : totalWidth xs ≤ n) :
    (flattenList xs).testBit n = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (flattenList_lt xs h) (two_pow_le_of_le hn))

/-! ### List-level mergePass -/

def mergePassList : List (Nat × Nat) → List (Nat × Nat)
  | (lo, lb) :: (hi, hb) :: rest =>
    (lo ||| (hi <<< lb), lb + hb) :: mergePassList rest
  | rest => rest

private theorem mergePassList_nil : mergePassList [] = [] := rfl

private theorem mergePassList_singleton (p : Nat × Nat) : mergePassList [p] = [p] := rfl

private theorem mergePassList_length (xs : List (Nat × Nat)) :
    (mergePassList xs).length = (xs.length + 1) / 2 := by
  match xs with
  | [] => rfl
  | [_] => simp [mergePassList]
  | (lo, lb) :: (hi, hb) :: rest =>
    simp only [mergePassList, List.length_cons]
    rw [mergePassList_length rest]; omega

private theorem mergePassList_wellFormed : ∀ (xs : List (Nat × Nat)),
    WellFormedList xs → WellFormedList (mergePassList xs)
  | [], _ => WellFormedList.nil
  | [p], h => h
  | (lo, lb) :: (hi, hb) :: rest, h => by
    have h_lo : lo < 2^lb := h (lo, lb) (by simp)
    have h_hi : hi < 2^hb := h (hi, hb) (by simp)
    have hrest : WellFormedList rest := fun q hq => h q (by simp [hq])
    have ihx := mergePassList_wellFormed rest hrest
    intro p hp
    simp only [mergePassList, List.mem_cons] at hp
    rcases hp with rfl | hp
    · apply Nat.or_lt_two_pow
      · exact Nat.lt_of_lt_of_le h_lo (two_pow_le_of_le (Nat.le_add_right _ _))
      · rw [Nat.shiftLeft_eq]
        have hmul : hi * 2^lb < 2^hb * 2^lb :=
          Nat.mul_lt_mul_of_pos_right h_hi (Nat.two_pow_pos lb)
        have heq : 2^hb * 2^lb = 2^(lb + hb) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [heq] at hmul; exact hmul
    · exact ihx p hp

private theorem flattenList_pack (lo lb hi hb : Nat) (rest : List (Nat × Nat))
    (h_lo : lo < 2^lb) :
    (lo ||| (hi <<< lb)) ||| (flattenList rest <<< (lb + hb))
      = lo ||| ((hi ||| (flattenList rest <<< hb)) <<< lb) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hjlb : lb ≤ j
  · have hlo_j : lo.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h_lo (two_pow_le_of_le hjlb))
    rw [hlo_j]
    simp only [Bool.false_or, hjlb, decide_true, Bool.true_and]
    by_cases hjlbhb : lb + hb ≤ j
    · simp only [hjlbhb, decide_true, Bool.true_and]
      have hhi_le : hb ≤ j - lb := by omega
      simp only [hhi_le, decide_true, Bool.true_and]
      have heq : j - (lb + hb) = j - lb - hb := by omega
      rw [heq]
    · simp only [hjlbhb, decide_false, Bool.false_and, Bool.or_false]
      have hhi_le : ¬ hb ≤ j - lb := by omega
      simp only [hhi_le, decide_false, Bool.false_and, Bool.or_false]
  · have hge2 : ¬ lb + hb ≤ j := by omega
    simp [hjlb, hge2]

private theorem flattenList_mergePassList : ∀ (xs : List (Nat × Nat)),
    WellFormedList xs → flattenList (mergePassList xs) = flattenList xs
  | [], _ => rfl
  | [_], _ => rfl
  | (lo, lb) :: (hi, hb) :: rest, h => by
    have h_lo : lo < 2^lb := h (lo, lb) (by simp)
    have hrest : WellFormedList rest := fun q hq => h q (by simp [hq])
    simp only [mergePassList, flattenList]
    rw [flattenList_mergePassList rest hrest]
    exact flattenList_pack lo lb hi hb rest h_lo

/-! ### Bridge Array `mergePass` ↔ List `mergePassList` -/

private theorem mergePass_go_toList_aux (arr : Array (Nat × Nat)) :
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
    rw [hdrop, mergePassList_nil, List.append_nil]
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
        rw [hdrop, mergePassList_singleton, Array.toList_push]
      · simp only [h2, ↓reduceDIte]
        have hdrop : arr.toList.drop i = [] :=
          List.drop_of_length_le (by simpa using Nat.le_of_not_lt h2)
        rw [hdrop, mergePassList_nil, List.append_nil]

private theorem mergePass_go_toList (arr : Array (Nat × Nat)) (i : Nat) (acc : Array (Nat × Nat)) :
    (mergePass.go arr i acc).toList = acc.toList ++ mergePassList (arr.toList.drop i) :=
  mergePass_go_toList_aux arr (arr.size - i) i acc (Nat.le_refl _)

private theorem mergePass_toList (arr : Array (Nat × Nat)) :
    (mergePass arr).toList = mergePassList arr.toList := by
  unfold mergePass
  rw [mergePass_go_toList]
  simp [Array.mkEmpty_eq]

private theorem mergePass_size (arr : Array (Nat × Nat)) :
    (mergePass arr).size = (arr.size + 1) / 2 := by
  rw [show (mergePass arr).size = (mergePass arr).toList.length from by simp]
  rw [mergePass_toList, mergePassList_length]
  simp

/-! ### treeMerge correctness -/

private theorem toList_size_one {arr : Array (Nat × Nat)} (h : arr.size = 1) :
    arr.toList = [arr[0]] := by
  apply List.ext_getElem (by simp [h])
  intro i hi1 hi2
  simp only [List.length_singleton] at hi2
  have : i = 0 := by omega
  subst this
  simp

private theorem toList_size_zero {arr : Array (Nat × Nat)} (h : arr.size = 0) :
    arr.toList = [] := by
  rw [Array.toList_eq_nil_iff]
  apply Array.eq_empty_of_size_eq_zero h

private theorem treeMerge_go_eq_flattenList (n : Nat) (arr : Array (Nat × Nat))
    (h : WellFormedList arr.toList) (hsize : arr.size ≤ 2^n) :
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
      have hwf' : WellFormedList (mergePass arr).toList := by
        rw [mergePass_toList]; exact mergePassList_wellFormed _ h
      have hsize' : (mergePass arr).size ≤ 2^k := by
        rw [mergePass_size]
        -- We need (arr.size + 1) / 2 ≤ 2^k from arr.size ≤ 2^(k+1) = 2^k + 2^k.
        have hpow : 2^(k+1) = 2^k + 2^k := Nat.two_pow_succ k
        rw [hpow] at hsize
        clear hpow ih h hwf'
        generalize 2^k = m at *
        omega
      rw [ih _ hwf' hsize', mergePass_toList]
      exact flattenList_mergePassList arr.toList h

private theorem treeMerge_eq_flattenList (arr : Array (Nat × Nat))
    (h : WellFormedList arr.toList) :
    treeMerge arr = flattenList arr.toList := by
  unfold treeMerge
  exact treeMerge_go_eq_flattenList _ _ h (Nat.le_of_lt Nat.lt_two_pow_self)

/-! ### collectChunks correctness -/

private theorem collectChunks_wellFormed (fuel : Nat) (bs : List Bool) (acc : Array (Nat × Nat))
    (hacc : WellFormedList acc.toList) :
    WellFormedList (collectChunks fuel bs acc).toList := by
  induction fuel generalizing bs acc with
  | zero =>
    cases bs with
    | nil => simpa [collectChunks] using hacc
    | cons _ _ => simpa [collectChunks] using hacc
  | succ k ih =>
    cases bs with
    | nil => simpa [collectChunks] using hacc
    | cons b bs =>
      simp only [collectChunks]
      apply ih
      rw [Array.toList_push]
      intro p hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact hacc p hp'
      · simp at hp'
        rw [hp']
        exact packChunk_init_lt (b :: bs) 64

/-- The strengthened spec for `collectChunks`. -/
private theorem testBit_flattenList_collectChunks_aux
    (fuel : Nat) (bs : List Bool) (acc : Array (Nat × Nat))
    (hfuel : bs.length ≤ fuel) (hacc : WellFormedList acc.toList) (i : Nat) :
    (flattenList (collectChunks fuel bs acc).toList).testBit i =
      if i < totalWidth acc.toList
      then (flattenList acc.toList).testBit i
      else bs.getD (i - totalWidth acc.toList) false := by
  induction fuel generalizing bs acc with
  | zero =>
    have hbs_nil : bs = [] := List.length_eq_zero_iff.mp (by omega)
    subst hbs_nil
    simp only [collectChunks]
    by_cases hi : i < totalWidth acc.toList
    · simp [hi]
    · simp only [hi, ↓reduceIte, List.getD_nil]
      exact testBit_flattenList_high _ hacc _ (Nat.le_of_not_lt hi)
  | succ k ih =>
    cases bs with
    | nil =>
      simp only [collectChunks]
      by_cases hi : i < totalWidth acc.toList
      · simp [hi]
      · simp only [hi, ↓reduceIte, List.getD_nil]
        exact testBit_flattenList_high _ hacc _ (Nat.le_of_not_lt hi)
    | cons b bs =>
      simp only [collectChunks]
      -- Use a `let` for the packed pieces; but to avoid `set`'s issues, work with explicit values.
      have hused_eq : (packChunk (b :: bs) 64 0 0).2.1 = min (b :: bs).length 64 := by
        rw [packChunk_used]; simp
      have hused_pos : 0 < (packChunk (b :: bs) 64 0 0).2.1 := by
        rw [hused_eq]; simp [List.length_cons]; omega
      have hrest_eq : (packChunk (b :: bs) 64 0 0).2.2 = (b :: bs).drop ((packChunk (b :: bs) 64 0 0).2.1) := by
        rw [packChunk_rest, hused_eq]
      have hchunk_lt : (packChunk (b :: bs) 64 0 0).1 < 2^((packChunk (b :: bs) 64 0 0).2.1) :=
        packChunk_init_lt _ _
      -- new acc well-formedness
      have hacc' : WellFormedList
          (acc.push ((packChunk (b :: bs) 64 0 0).1, (packChunk (b :: bs) 64 0 0).2.1)).toList := by
        rw [Array.toList_push]
        intro p hp
        rcases List.mem_append.mp hp with hp' | hp'
        · exact hacc p hp'
        · simp at hp'; rw [hp']; exact hchunk_lt
      -- rest length is ≤ k for IH
      have hrest_len : (packChunk (b :: bs) 64 0 0).2.2.length ≤ k := by
        rw [hrest_eq, List.length_drop, hused_eq]
        clear hchunk_lt
        simp only [List.length_cons] at hfuel ⊢
        omega
      -- totalWidth after push
      have htw_push :
          totalWidth (acc.push ((packChunk (b :: bs) 64 0 0).1, (packChunk (b :: bs) 64 0 0).2.1)).toList
          = totalWidth acc.toList + (packChunk (b :: bs) 64 0 0).2.1 := by
        rw [Array.toList_push, totalWidth_append]
        simp [totalWidth]
      -- flattenList after push
      have hflat_push :
          flattenList (acc.push ((packChunk (b :: bs) 64 0 0).1, (packChunk (b :: bs) 64 0 0).2.1)).toList
          = flattenList acc.toList |||
              ((packChunk (b :: bs) 64 0 0).1 <<< totalWidth acc.toList) := by
        rw [Array.toList_push, flattenList_append, flattenList_singleton]
      -- Apply IH
      have ih' := ih (packChunk (b :: bs) 64 0 0).2.2
        (acc.push ((packChunk (b :: bs) 64 0 0).1, (packChunk (b :: bs) 64 0 0).2.1)) hrest_len hacc'
      rw [ih', htw_push]
      -- Three-way case split on i
      by_cases h1 : i < totalWidth acc.toList
      · have h1' : i < totalWidth acc.toList + (packChunk (b :: bs) 64 0 0).2.1 := by
          have := hused_pos; omega
        simp only [h1, ↓reduceIte, h1', ↓reduceIte]
        rw [hflat_push, Nat.testBit_or, Nat.testBit_shiftLeft]
        have hge : ¬ totalWidth acc.toList ≤ i := Nat.not_le_of_lt h1
        simp [hge]
      · have hge : totalWidth acc.toList ≤ i := Nat.le_of_not_lt h1
        simp only [h1, ↓reduceIte]
        by_cases h2 : i < totalWidth acc.toList + (packChunk (b :: bs) 64 0 0).2.1
        · simp only [h2, ↓reduceIte]
          rw [hflat_push, Nat.testBit_or]
          rw [testBit_flattenList_high _ hacc _ hge, Bool.false_or]
          rw [Nat.testBit_shiftLeft]
          simp only [hge, decide_true, Bool.true_and]
          have hjr : i - totalWidth acc.toList < min (b :: bs).length 64 := by
            rw [← hused_eq]; omega
          exact packChunk_init_testBit (b :: bs) 64 (i - totalWidth acc.toList) hjr
        · have h2' : ¬ i < totalWidth acc.toList + (packChunk (b :: bs) 64 0 0).2.1 := h2
          simp only [h2', ↓reduceIte]
          -- bridge: (rest).getD (i - (tw + used)) false = (b :: bs).getD (i - tw) false
          rw [hrest_eq]
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          rw [List.getElem?_drop]
          congr 2
          omega

private theorem testBit_flattenList_collectChunks (bs : List Bool) (i : Nat) :
    (flattenList ((collectChunks bs.length bs
        (Array.mkEmpty ((bs.length + 63) / 64))).toList)).testBit i = bs.getD i false := by
  have hempty :
      ((Array.mkEmpty ((bs.length + 63) / 64) : Array (Nat × Nat))).toList = [] := by
    simp [Array.mkEmpty_eq]
  have hwf : WellFormedList ((Array.mkEmpty ((bs.length + 63) / 64) :
      Array (Nat × Nat))).toList := by
    rw [hempty]; exact WellFormedList.nil
  rw [testBit_flattenList_collectChunks_aux _ _ _ (Nat.le_refl _) hwf]
  rw [hempty]
  simp [totalWidth]

/-! ### Main correctness theorems -/

private theorem getLsbD_ofBoolListLEImpl (bs : List Bool) (i : Nat) (hi : i < bs.length) :
    (ofBoolListLEImpl bs).getLsbD i = bs.getD i false := by
  unfold ofBoolListLEImpl
  rw [getLsbD_ofNat]
  simp only [hi, decide_true, Bool.true_and]
  have hwf : WellFormedList ((collectChunks bs.length bs
      (Array.mkEmpty ((bs.length + 63) / 64))).toList) := by
    apply collectChunks_wellFormed
    rw [show ((Array.mkEmpty ((bs.length + 63) / 64) :
      Array (Nat × Nat))).toList = [] from by simp [Array.mkEmpty_eq]]
    exact WellFormedList.nil
  rw [treeMerge_eq_flattenList _ hwf]
  exact testBit_flattenList_collectChunks bs i

private theorem getLsbD_ofBoolListBEImpl (bs : List Bool) (i : Nat) (hi : i < bs.length) :
    (ofBoolListBEImpl bs).getLsbD i =
      (decide (i < bs.length) && bs.getD (bs.length - 1 - i) false) := by
  unfold ofBoolListBEImpl
  rw [BitVec.getLsbD_cast]
  have hi' : i < bs.reverse.length := by simpa using hi
  rw [getLsbD_ofBoolListLEImpl bs.reverse i hi']
  simp only [hi, decide_true, Bool.true_and]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_reverse hi]

end BitVec.Internal

namespace BitVec

@[csimp]
theorem ofBoolListLE_eq_impl : @ofBoolListLE = @BitVec.Internal.ofBoolListLEImpl := by
  funext bs
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBoolListLE]
  exact (BitVec.Internal.getLsbD_ofBoolListLEImpl bs i hi).symm

@[csimp]
theorem ofBoolListBE_eq_impl : @ofBoolListBE = @BitVec.Internal.ofBoolListBEImpl := by
  funext bs
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBoolListBE]
  exact (BitVec.Internal.getLsbD_ofBoolListBEImpl bs i hi).symm

end BitVec
