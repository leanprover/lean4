/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

prelude
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Bool
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Div.Lemmas
import Init.Data.Int.Pow -- Used by omega when normalizing powers.
import Init.ByCases
import Init.RCases
import Init.Omega
import Init.Data.List.Lemmas

/-!
# Population count

The kernel-reducible implementation counts bits in parallel across a natural number. Packed
byte counts are combined into wider lanes; reduction modulo one less than the lane base then
sums the lanes. The bytewise algorithm and proof are adapted from Bhavik Mehta's `PrimeCert.PopCount`.
-/
namespace Nat
namespace popcount

/-- Replace each byte by its bit count. `ones` is an all-ones mask covering the input. -/
@[expose, implicit_reducible] public def bytes (n ones : Nat) : Nat :=
  let a := n.sub ((n.shiftRight 1).land (ones.div 3))
  let b := (a.land (ones.div 5)).add ((a.shiftRight 2).land (ones.div 5))
  (b.add (b.shiftRight 4)).land (ones.div 17)

/-- Combine adjacent lanes until their base exceeds the maximum total count, then sum them
by taking the remainder modulo one less than that base. -/
@[expose, implicit_reducible] public noncomputable def fold : Nat → Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (fun _ _ _ _ => 0) (fun _ rec width ones lane n =>
    (width.blt ((Nat.shiftLeft 1 lane).sub 1)).rec
      (rec width ones (lane.add lane)
        ((n.add (n.shiftRight lane)).land (ones.div ((Nat.shiftLeft 1 lane).add 1))))
      (n.mod ((Nat.shiftLeft 1 lane).sub 1)))

/-- Count an input covered by `width` bits, where `width` is eight times a power of two. -/
@[expose, implicit_reducible] public noncomputable def wide (n width : Nat) : Nat :=
  let ones := (Nat.shiftLeft 1 width).sub 1
  fold width width ones 8 (bytes n ones)

/-- Double the width until it covers the input. The base case uses the final width directly. -/
@[expose, implicit_reducible] public noncomputable def grow : Nat → Nat → Nat → Nat :=
  Nat.rec (fun n width => wide n width) (fun _ rec n width =>
    ((n.shiftRight width).beq 0).rec
      (rec n (width.add width)) (wide n width))

/-- Count an input of at most 248 bits using byte lanes and precomputed masks.
The total is strictly less than 255, so the final remainder recovers it exactly. -/
@[expose, implicit_reducible] public def small (v : Nat) : Nat :=
  let a := v.sub
    ((v.shiftRight 1).land 0x55555555555555555555555555555555555555555555555555555555555555)
  let b := (a.land 0x33333333333333333333333333333333333333333333333333333333333333).add
    ((a.shiftRight 2).land 0x33333333333333333333333333333333333333333333333333333333333333)
  let c := (b.add (b.shiftRight 4)).land
    0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
  c.mod 255

/-- Count an input covered by `width` bits using 16-bit lanes.
Used at widths 256 and 4096. -/
@[expose, implicit_reducible] public def word16 (n width : Nat) : Nat :=
  let ones := (Nat.shiftLeft 1 width).sub 1
  let c := bytes n ones
  ((c.add (c.shiftRight 8)).land (ones.div 257)).mod 65535

/-- Count an input of at most 65536 bits using 32-bit lanes. -/
@[expose, implicit_reducible] public def word32 (n : Nat) : Nat :=
  let ones := (Nat.shiftLeft 1 65536).sub 1
  let c := bytes n ones
  let d := (c.add (c.shiftRight 8)).land (ones.div 257)
  ((d.add (d.shiftRight 16)).land (ones.div 65537)).mod 4294967295

end popcount

/-- The number of set bits in the binary representation of a natural number.
Kernel reduction counts bits in parallel using existing natural-number arithmetic.
The compiled implementation scans machine limbs. -/
@[expose, implicit_reducible, extern "lean_nat_popcount"] public def popcount (n : @& Nat) : Nat :=
  ((n.shiftRight 248).beq 0).rec
    (((n.shiftRight 256).beq 0).rec
      (((n.shiftRight 4096).beq 0).rec
        (((n.shiftRight 65536).beq 0).rec (popcount.grow n.succ n 131072) (popcount.word32 n))
        (popcount.word16 n 4096))
      (popcount.word16 n 256))
    (popcount.small n)

namespace popcount

/-- Binary specification used only in the correctness proof. -/
def count (n : Nat) : Nat :=
  if n = 0 then 0 else count (n / 2) + n % 2
termination_by n
decreasing_by omega

@[simp] theorem count_zero : count 0 = 0 := by rw [count]; rfl

theorem count_div_two (n : Nat) : count n = count (n / 2) + n % 2 := by
  rw [count]
  split <;> simp_all

/-- Splitting at any binary digit adds the counts of the two parts. -/
theorem count_mul_two_pow_add (a k b : Nat) (hb : b < 2 ^ k) :
    count (a * 2 ^ k + b) = count a + count b := by
  induction k generalizing b with
  | zero =>
    have : b = 0 := by simpa using hb
    subst b
    simp
  | succ k ih =>
    rw [count_div_two (a * 2 ^ (k + 1) + b), count_div_two b]
    rw [Nat.pow_succ] at hb ⊢
    rw [show a * (2 ^ k * 2) = 2 * (a * 2 ^ k) by simp only [Nat.mul_comm, Nat.mul_left_comm],
      Nat.mul_add_div (by decide), Nat.mul_add_mod]
    rw [ih (b / 2) (by omega), Nat.add_assoc]

theorem count_mod_add_div (n k : Nat) :
    count (n % 2 ^ k) + count (n / 2 ^ k) = count n := by
  have h := count_mul_two_pow_add (n / 2 ^ k) k (n % 2 ^ k)
    (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [Nat.mul_comm (n / 2 ^ k), Nat.div_add_mod] at h
  omega

theorem count_le_of_lt_two_pow {n k : Nat} (h : n < 2 ^ k) : count n ≤ k := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using h
    subst n
    simp
  | succ k ih =>
    rw [count_div_two]
    have hh := ih (n := n / 2) (by rw [Nat.pow_succ] at h; omega)
    omega

variable {v m s b k n : Nat}

/-! ## Splitting bitwise operations at a bit boundary -/

theorem land_split :
    v &&& m = (v % 2 ^ s &&& m % 2 ^ s) + 2 ^ s * (v / 2 ^ s &&& m / 2 ^ s) := by
  rw [← Nat.and_mod_two_pow, ← Nat.and_div_two_pow, Nat.mod_add_div]

theorem land_parts (ha : a < 2 ^ s) (hb : b < 2 ^ s) :
    (a + 2 ^ s * c) &&& (b + 2 ^ s * d) = (a &&& b) + 2 ^ s * (c &&& d) := by
  rw [land_split (s := s)]
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt ha,
    Nat.div_eq_of_lt hb, Nat.zero_add]

theorem shiftLeft_land_shiftRight :
    ((v >>> s) &&& m) <<< s = v &&& (m <<< s) :=
  Nat.eq_of_testBit_eq fun j ↦ by
    by_cases h : s ≤ j
    · simp [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, h,
        Nat.add_sub_cancel' h]
    · simp [Nat.testBit_shiftLeft, Nat.testBit_and, h]

theorem land_15 : v &&& 15 = v % 16 := Nat.and_two_pow_sub_one_eq_mod v 4

/-! ## The three stages

`rep b k` is the `k`-byte constant repeating the byte `b`. The three stages use masks
`rep 85 k`, `rep 51 k` and `rep 15 k`. -/

/-- The `k`-byte constant repeating the byte `b`. -/
def rep (b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => b + 256 * rep b k

/-- Counts within 2-bit groups of a `k`-byte value. -/
def stageA (v k : Nat) : Nat := v - (v >>> 1 &&& rep 85 k)

/-- Counts within 4-bit groups of a `k`-byte value. -/
def stageB (v k : Nat) : Nat := (stageA v k &&& rep 51 k) + (stageA v k >>> 2 &&& rep 51 k)

/-- Counts within 8-bit groups. -/
def stageC (v k : Nat) : Nat := (stageB v k + (stageB v k >>> 4)) &&& rep 15 k

@[simp] theorem rep_succ : rep b (k + 1) = b + 256 * rep b k := rfl

@[simp] theorem rep_zero : rep b 0 = 0 := rfl

@[simp] theorem rep_one : rep b 1 = b := rfl

theorem rep_shiftLeft : rep b k <<< s = rep (b <<< s) k := by
  simp only [Nat.shiftLeft_eq]
  induction k with
  | zero => simp
  | succ k ih => simp only [rep_succ, Nat.add_mul, Nat.mul_assoc, ih]

/-- A repeated-byte mask splits at the byte boundary. -/
theorem land_rep_succ (hm : m < 256) :
    v &&& rep m (k + 1) = (v % 256 &&& m) + 256 * (v / 256 &&& rep m k) := by
  rw [land_split (s := 8)]
  simp only [show 2 ^ 8 = 256 from rfl, rep_succ, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by decide : 0 < 256), Nat.mod_eq_of_lt hm,
    Nat.div_eq_of_lt hm, Nat.zero_add]

/-- `rep 1 k` fills `k` bytes with ones. -/
theorem rep_one_mul : 255 * rep 1 k + 1 = 256 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, Nat.pow_succ]; omega

@[simp] theorem stageB_zero : stageB v 0 = 0 := by simp [stageB]
@[simp] theorem stageC_zero : stageC v 0 = 0 := by simp [stageC]

/-- On a byte the stages stay inside the byte, and the last one holds its set-bit count. -/
theorem byte_pipeline (hv : v < 256) :
    stageA v 1 < 256 ∧ stageB v 1 ≤ 68 ∧ stageB v 1 % 16 ≤ 4 ∧
      stageC v 1 = count v := by
  have h : ∀ v : Fin 256, stageA v 1 < 256 ∧ stageB v 1 ≤ 68 ∧
      stageB v 1 % 16 ≤ 4 ∧ stageC v 1 = count v := by decide +kernel
  exact h ⟨v, hv⟩

theorem stageA_byte_lt (hv : v < 256) : stageA v 1 < 256 := (byte_pipeline hv).1

theorem stageB_byte_le (hv : v < 256) : stageB v 1 ≤ 68 := (byte_pipeline hv).2.1

theorem stageB_byte_mod_16 (hv : v < 256) : stageB v 1 % 16 ≤ 4 := (byte_pipeline hv).2.2.1

theorem stageC_byte_eq (hv : v < 256) : stageC v 1 = count v := (byte_pipeline hv).2.2.2

/-! ## Peeling one byte -/

theorem shiftRight_land_parts (ha : a < 256) (hms : m <<< s < 256) :
    ((a + 256 * b) >>> s) &&& rep m (k + 1) =
      ((a >>> s) &&& m) + 256 * ((b >>> s) &&& rep m k) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos s)
  have h := land_parts (s := 8) (c := b) (d := rep (m <<< s) k) ha hms
  change (a + 256 * b) &&& ((m <<< s) + 256 * rep (m <<< s) k) =
    (a &&& (m <<< s)) + 256 * (b &&& rep (m <<< s) k) at h
  rw [← rep_succ] at h
  simp only [← rep_shiftLeft, ← shiftLeft_land_shiftRight] at h
  simpa only [Nat.shiftLeft_eq, Nat.add_mul, Nat.mul_assoc] using h

theorem stageA_split (v k : Nat) :
    stageA v (k + 1) = stageA (v % 256) 1 + 256 * stageA (v / 256) k := by
  have lo := Nat.le_trans (Nat.and_le_left (n := (v % 256) >>> 1) (m := rep 85 1))
    (Nat.shiftRight_le (v % 256) 1)
  have hi := Nat.le_trans (Nat.and_le_left (n := (v / 256) >>> 1) (m := rep 85 k))
    (Nat.shiftRight_le (v / 256) 1)
  unfold stageA
  conv => lhs; rw [← Nat.mod_add_div v 256]
  rw [shiftRight_land_parts (Nat.mod_lt _ (by decide)) (by decide)]
  simp only [rep_one] at lo ⊢
  omega

theorem stageB_split (v k : Nat) :
    stageB v (k + 1) = stageB (v % 256) 1 + 256 * stageB (v / 256) k := by
  have hlo := stageA_byte_lt (v := v % 256) (Nat.mod_lt _ (by decide))
  simp only [stageB]
  rw [stageA_split, shiftRight_land_parts hlo (by decide), rep_succ,
    land_parts (s := 8) hlo (by decide)]
  simp only [rep_one]
  omega

theorem stageB_mod_16 (v k : Nat) : stageB v k % 16 ≤ 4 := by
  cases k with
  | zero => simp
  | succ k =>
    have h := stageB_byte_mod_16 (v := v % 256) (Nat.mod_lt _ (by omega))
    rw [stageB_split]
    omega

/-- The final mask discards cross-byte carries using the previous stage's bounds. -/
theorem stageC_split (v k : Nat) :
    stageC v (k + 1) = stageC (v % 256) 1 + 256 * stageC (v / 256) k := by
  have hlo := stageB_byte_le (v := v % 256) (Nat.mod_lt _ (by decide))
  have hhi := stageB_mod_16 (v / 256) k
  simp only [stageC, rep_one]
  rw [stageB_split]
  rw [land_rep_succ (by decide)]
  simp only [land_15, Nat.shiftRight_eq_div_pow]
  congr 1
  · omega
  · congr 1; congr 1; omega

/-! ## Packed lanes

These lists occur only in the correctness proof. The executable works on one natural number,
with no list allocation or per-lane recursion.
-/
def pack (s : Nat) : List Nat → Nat
  | [] => 0
  | a :: xs => a + 2 ^ s * pack s xs

def pairs : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: b :: xs => (a + b) :: pairs xs

def stripe (s : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (2 ^ s - 1) + 2 ^ (s + s) * stripe s k

theorem pack_cons_div (ha : a < 2 ^ s) : pack s (a :: xs) / 2 ^ s = pack s xs := by
  simp only [pack, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt ha,
    Nat.zero_add]

theorem pairs_sum (xs : List Nat) : (pairs xs).sum = xs.sum := by
  induction xs using pairs.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih => simp only [pairs, List.sum_cons, ih, Nat.add_assoc]

theorem pairs_length (xs : List Nat) : (pairs xs).length = (xs.length + 1) / 2 := by
  induction xs using pairs.induct with
  | case1 => rfl
  | case2 a => simp [pairs]
  | case3 a b xs ih => simp only [pairs, List.length_cons, ih]; omega

theorem pairs_bound (h : ∀ a ∈ xs, a ≤ s) : ∀ a ∈ pairs xs, a ≤ s + s := by
  induction xs using pairs.induct with
  | case1 => simp [pairs]
  | case2 a => simpa [pairs] using Nat.le_add_right_of_le (h a (by simp))
  | case3 a b xs ih =>
    simp only [pairs, List.forall_mem_cons] at h ⊢
    exact ⟨by omega, ih h.2.2⟩

/-- The alternating mask retains disjoint sums; the bounds rule out carries. -/
theorem pack_merge (hlen : xs.length = 2 * k) (h : ∀ a ∈ xs, a ≤ s)
    (hs : s + s < 2 ^ s) :
    (pack s xs + pack s xs / 2 ^ s) &&& stripe s k = pack (s + s) (pairs xs) := by
  induction k generalizing xs with
  | zero =>
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    simp [pack, stripe, pairs]
  | succ k ih =>
    match xs with
    | [] | [_] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | a :: b :: xs =>
      simp only [List.forall_mem_cons] at h
      obtain ⟨ha, hb, hx⟩ := h
      have hl : xs.length = 2 * k := by simp only [List.length_cons] at hlen; omega
      have hd : pack s xs / 2 ^ s = pack s xs.tail := by
        cases xs with
        | nil => simp [pack]
        | cons c xs => exact pack_cons_div (by have := hx c (by simp); omega)
      have hh : xs.headD 0 ≤ s := by
        cases xs with
        | nil => simp
        | cons c xs => exact hx c (by simp)
      have hp : pack s xs = xs.headD 0 + 2 ^ s * pack s xs.tail := by cases xs <;> rfl
      have hlo : a + b + 2 ^ s * (b + xs.headD 0) < 2 ^ (s + s) := by
        have := Nat.mul_le_mul_left (2 ^ s) (show b + xs.headD 0 + 1 ≤ 2 ^ s by omega)
        rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_add] at this
        omega
      have hm : 2 ^ s - 1 < 2 ^ (s + s) := by
        have := Nat.pow_le_pow_right (by decide : 0 < 2) (show s ≤ s + s by omega)
        have := Nat.two_pow_pos s
        omega
      simp only [pack, pairs, stripe]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt (by omega : a < 2 ^ s)]
      rw [show a + 2 ^ s * (b + 2 ^ s * pack s xs) + (0 + (b + 2 ^ s * pack s xs)) =
          (a + b + 2 ^ s * (b + xs.headD 0)) + 2 ^ (s + s) * (pack s xs + pack s xs.tail) by
        rw [hp]
        simp only [Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.zero_add]
        omega]
      rw [land_parts hlo hm, ← hd, ih hl hx,
        Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega : a + b < 2 ^ s)]

theorem stripe_mul (s k : Nat) :
    (2 ^ s + 1) * stripe s k + 1 = 2 ^ ((s + s) * k) := by
  induction k with
  | zero => simp [stripe]
  | succ k ih =>
    have hc := Nat.mul_self_sub_mul_self_eq (2 ^ s) 1
    have hp := Nat.mul_pos (Nat.two_pow_pos s) (Nat.two_pow_pos s)
    rw [stripe, Nat.mul_succ, Nat.pow_add 2 ((s + s) * k), ← ih, Nat.pow_add 2 s s]
    generalize 2 ^ s = p at hc hp ⊢
    rw [Nat.mul_add, ← hc, Nat.mul_left_comm (p + 1),
      Nat.add_mul ((p + 1) * stripe s k) 1 (p * p), Nat.mul_comm ((p + 1) * stripe s k) (p * p)]
    omega

theorem stripe_eq (s k : Nat) : stripe s k = (2 ^ ((s + s) * k) - 1) / (2 ^ s + 1) := by
  have h := stripe_mul s k
  have hh : 2 ^ ((s + s) * k) - 1 = (2 ^ s + 1) * stripe s k := by omega
  rw [hh, Nat.mul_div_right _ (Nat.zero_lt_succ _)]

theorem pack_mod (xs : List Nat) : pack s xs % (2 ^ s - 1) = xs.sum % (2 ^ s - 1) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have hp := Nat.two_pow_pos s
    have hh : 2 ^ s = (2 ^ s - 1) + 1 := by omega
    simp only [pack, List.sum_cons]
    rw [show a + 2 ^ s * pack s xs = (2 ^ s - 1) * pack s xs + (a + pack s xs) by
      conv => lhs; rw [hh, Nat.add_mul, Nat.one_mul]
      omega]
    rw [Nat.mul_add_mod, ← Nat.add_mod_mod, ih, Nat.add_mod_mod]

theorem rep_mul (b k : Nat) : rep b k = b * rep 1 k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [rep_succ, ih, Nat.mul_add, Nat.mul_one]; simp only [Nat.mul_left_comm]

theorem bytes_eq (n k : Nat) : bytes n (2 ^ (8 * k) - 1) = stageC n k := by
  have hh : 2 ^ (8 * k) - 1 = 255 * rep 1 k := by
    have := rep_one_mul (k := k)
    rw [Nat.pow_mul]
    change 256 ^ k - 1 = 255 * rep 1 k
    omega
  have mask (d b : Nat) (hd : 0 < d) (h : d * b = 255) :
      (255 * rep 1 k).div d = rep b k := by
    change (255 * rep 1 k) / d = rep b k
    rw [← h, Nat.mul_assoc, Nat.mul_div_right _ hd, rep_mul b k]
  simp only [bytes, hh, mask 3 85 (by decide) (by decide),
    mask 5 51 (by decide) (by decide), mask 17 15 (by decide) (by decide)]
  rfl

def byteDigits : Nat → Nat → List Nat
  | _, 0 => []
  | n, k + 1 => count (n % 256) :: byteDigits (n / 256) k

theorem byteDigits_length (n k : Nat) : (byteDigits n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [byteDigits, List.length_cons, ih]

theorem byteDigits_bound (n k : Nat) : ∀ a ∈ byteDigits n k, a ≤ 8 := by
  induction k generalizing n with
  | zero => simp [byteDigits]
  | succ k ih =>
    simp only [byteDigits, List.forall_mem_cons]
    exact ⟨count_le_of_lt_two_pow (Nat.mod_lt _ (by decide)), ih _⟩

theorem byteDigits_pack (n k : Nat) : pack 8 (byteDigits n k) = stageC n k := by
  induction k generalizing n with
  | zero => simp [byteDigits, pack]
  | succ k ih =>
    simp only [byteDigits, pack, ih]
    rw [stageC_split, stageC_byte_eq (Nat.mod_lt _ (by decide))]

theorem byteDigits_sum (hn : n < 2 ^ (8 * k)) : (byteDigits n k).sum = count n := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n
    simp [byteDigits]
  | succ k ih =>
    have hh : n / 256 < 2 ^ (8 * k) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add] at hn
      omega
    simp only [byteDigits, List.sum_cons, ih hh]
    exact count_mod_add_div n 8

theorem sum_le {xs : List Nat} {s : Nat} (h : ∀ a ∈ xs, a ≤ s) : xs.sum ≤ s * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.forall_mem_cons] at h
    simpa [Nat.mul_succ, Nat.add_comm] using Nat.add_le_add h.1 (ih h.2)

theorem lane_bound (hs : 8 ≤ s) : s + s < 2 ^ s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have := Nat.lt_two_pow_self (n := t)
  rw [Nat.pow_add]
  omega

/-- Each lane stores at most its original bit width. Pairing lanes preserves the total and
this bound; the stopping test makes reduction modulo the lane base minus one exact. -/
theorem fold_eq (hf : k < fuel) (hlen : xs.length = 2 ^ k) (hb : ∀ a ∈ xs, a ≤ s)
    (hs : 8 ≤ s) : fold fuel (s * 2 ^ k) (2 ^ (s * 2 ^ k) - 1) s (pack s xs) = xs.sum := by
  induction fuel generalizing k s xs with
  | zero => omega
  | succ fuel ih =>
    change Bool.rec (motive := fun _ => Nat)
      (fold fuel (s * 2 ^ k) (2 ^ (s * 2 ^ k) - 1) (s + s)
        ((pack s xs + (pack s xs >>> s)) &&& ((2 ^ (s * 2 ^ k) - 1) / ((1 <<< s) + 1))))
      (pack s xs % ((1 <<< s) - 1)) ((s * 2 ^ k).blt ((1 <<< s) - 1)) = xs.sum
    simp only [Nat.one_shiftLeft]
    have hsum := sum_le hb
    rw [hlen] at hsum
    cases h : (s * 2 ^ k).blt (2 ^ s - 1) with
    | true =>
      dsimp only
      have hh : s * 2 ^ k < 2 ^ s - 1 := Nat.blt_eq.mp h
      rw [pack_mod, Nat.mod_eq_of_lt (by omega)]
    | false =>
      dsimp only
      have hh : ¬ s * 2 ^ k < 2 ^ s - 1 := by intro hh; have := Nat.blt_eq.mpr hh; simp [h] at this
      cases k with
      | zero => have := lane_bound hs; simp only [Nat.pow_zero, Nat.mul_one] at hh; omega
      | succ k =>
        have hw : s * 2 ^ (k + 1) = (s + s) * 2 ^ k := by
          simp only [Nat.pow_succ, Nat.add_mul, ← Nat.mul_assoc]; omega
        rw [hw, ← stripe_eq, Nat.shiftRight_eq_div_pow,
          pack_merge (by rw [hlen, Nat.pow_succ, Nat.mul_comm]) hb (lane_bound hs)]
        apply Eq.trans (ih (k := k) (s := s + s) (xs := pairs xs) (by omega)
          (by rw [pairs_length, hlen, Nat.pow_succ]; omega) (pairs_bound hb) (by omega))
        exact pairs_sum xs

theorem wide_eq (hn : n < 2 ^ (8 * 2 ^ k)) : wide n (8 * 2 ^ k) = count n := by
  change fold (8 * 2 ^ k) (8 * 2 ^ k) ((1 <<< (8 * 2 ^ k)) - 1) 8
    (bytes n ((1 <<< (8 * 2 ^ k)) - 1)) = count n
  rw [Nat.one_shiftLeft, bytes_eq, ← byteDigits_pack]
  rw [fold_eq (by have := Nat.lt_two_pow_self (n := k); omega)
    (byteDigits_length n (2 ^ k)) (byteDigits_bound n (2 ^ k)) (by decide), byteDigits_sum hn]

theorem grow_eq (hn : n < 2 ^ (8 * 2 ^ k + fuel)) : grow fuel n (8 * 2 ^ k) = count n := by
  induction fuel generalizing k with
  | zero => exact wide_eq (by simpa using hn)
  | succ fuel ih =>
    change Bool.rec (motive := fun _ => Nat)
      (grow fuel n ((8 * 2 ^ k) + (8 * 2 ^ k))) (wide n (8 * 2 ^ k))
      ((n >>> (8 * 2 ^ k)).beq 0) = count n
    cases h : (n >>> (8 * 2 ^ k)).beq 0 with
    | true =>
      dsimp only
      have hh : n / 2 ^ (8 * 2 ^ k) = 0 := by
        simpa only [Nat.beq_eq, Nat.shiftRight_eq_div_pow] using h
      exact wide_eq (Nat.lt_of_div_eq_zero (Nat.two_pow_pos _) hh)
    | false =>
      dsimp only
      rw [show 8 * 2 ^ k + 8 * 2 ^ k = 8 * 2 ^ (k + 1) by rw [Nat.pow_succ]; omega]
      apply ih
      have hp := Nat.two_pow_pos k
      have hm : 8 * 2 ^ k + (fuel + 1) ≤ 8 * 2 ^ (k + 1) + fuel := by rw [Nat.pow_succ]; omega
      exact Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hm)

set_option exponentiation.threshold 65536

theorem small_eq (hn : n < 2 ^ 248) : small n = count n := by
  change bytes n (2 ^ (8 * 31) - 1) % (2 ^ 8 - 1) = count n
  rw [bytes_eq, ← byteDigits_pack, pack_mod, byteDigits_sum hn]
  have h := count_le_of_lt_two_pow hn
  exact Nat.mod_eq_of_lt (by omega)

theorem word16_eq_256 (hn : n < 2 ^ 256) : word16 n 256 = count n := by
  change wide n (8 * 2 ^ 5) = count n
  exact wide_eq hn

theorem word16_eq_4096 (hn : n < 2 ^ 4096) : word16 n 4096 = count n := by
  change wide n (8 * 2 ^ 9) = count n
  exact wide_eq hn

theorem word32_eq (hn : n < 2 ^ 65536) : word32 n = count n := by
  change wide n (8 * 2 ^ 13) = count n
  exact wide_eq hn

theorem count_eq (n : Nat) : Nat.popcount n = count n := by
  have bound (k : Nat) (h : (n.shiftRight k).beq 0 = true) : n < 2 ^ k := by
    have hh : n >>> k = 0 := Nat.eq_of_beq_eq_true h
    rw [Nat.shiftRight_eq_div_pow] at hh
    exact Nat.lt_of_div_eq_zero (Nat.two_pow_pos _) hh
  unfold Nat.popcount
  cases h248 : (n.shiftRight 248).beq 0 with
  | true => exact small_eq (bound _ h248)
  | false =>
    cases h256 : (n.shiftRight 256).beq 0 with
    | true => exact word16_eq_256 (bound _ h256)
    | false =>
      cases h4096 : (n.shiftRight 4096).beq 0 with
      | true => exact word16_eq_4096 (bound _ h4096)
      | false =>
        cases h65536 : (n.shiftRight 65536).beq 0 with
        | true => exact word32_eq (bound _ h65536)
        | false =>
          exact grow_eq (k := 14) (Nat.lt_of_lt_of_le (Nat.lt_two_pow_self (n := n))
            (Nat.pow_le_pow_right (by decide) (by omega)))

end popcount

@[simp] public theorem popcount_zero : popcount 0 = 0 := by
  simpa only [popcount.count_eq] using popcount.count_zero

public theorem popcount_div_two (n : Nat) : popcount n = popcount (n / 2) + n % 2 := by
  simpa only [popcount.count_eq] using popcount.count_div_two n

@[simp] public theorem popcount_one : popcount 1 = 1 := by
  rw [popcount_div_two]
  simp

@[simp] public theorem popcount_bool (b : Bool) : popcount b.toNat = b.toNat := by
  cases b <;> simp

@[simp] public theorem popcount_two_mul_add (n : Nat) (b : Bool) :
    popcount (2 * n + b.toNat) = popcount n + b.toNat := by
  rw [popcount_div_two]
  have hb := b.toNat_lt
  rw [show (2 * n + b.toNat) / 2 = n by omega,
    show (2 * n + b.toNat) % 2 = b.toNat by omega]

/-- Splitting at any binary digit adds the counts of the two parts. -/
public theorem popcount_mul_two_pow_add (a k b : Nat) (hb : b < 2 ^ k) :
    popcount (a * 2 ^ k + b) = popcount a + popcount b := by
  simpa only [popcount.count_eq] using popcount.count_mul_two_pow_add a k b hb

public theorem popcount_mod_add_div (n k : Nat) :
    popcount (n % 2 ^ k) + popcount (n / 2 ^ k) = popcount n := by
  simpa only [popcount.count_eq] using popcount.count_mod_add_div n k

public theorem popcount_le_of_lt_two_pow {n k : Nat} (h : n < 2 ^ k) : popcount n ≤ k := by
  simpa only [popcount.count_eq] using popcount.count_le_of_lt_two_pow h

public theorem popcount_le (n : Nat) : popcount n ≤ n :=
  popcount_le_of_lt_two_pow Nat.lt_two_pow_self

end Nat
