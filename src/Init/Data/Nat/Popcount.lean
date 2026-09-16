/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
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
import Init.WFTactics
import Init.Data.List.Lemmas

/-!
# Population count

The kernel-reducible implementation counts bits in parallel across a natural number. Packed
byte counts are combined into wider lanes; reduction modulo one less than the lane base then
sums the lanes. The bytewise algorithm and proof follow Bhavik Mehta's `PrimeCert.PopCount`.
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

/-- Count an input of at most 64 bits using byte lanes. -/
@[expose, implicit_reducible] public def small (n : Nat) : Nat :=
  (bytes n 0xffffffffffffffff).mod 255

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
  ((n.shiftRight 64).beq 0).rec
    (((n.shiftRight 256).beq 0).rec
      (((n.shiftRight 4096).beq 0).rec
        (((n.shiftRight 65536).beq 0).rec (popcount.grow n.succ n 131072) (popcount.word32 n))
        (popcount.word16 n 4096))
      (popcount.word16 n 256))
    (popcount.small n)

namespace popcount

/-- Binary specification used to prove the parallel counting algorithm. -/
def count (n : Nat) : Nat :=
  if h : n = 0 then 0 else count (n / 2) + n % 2
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by decide)

@[simp] theorem count_zero : count 0 = 0 := by rw [count]; rfl

theorem count_div_two (n : Nat) : count n = count (n / 2) + n % 2 := by
  rw [count]
  split
  · next h => subst n; simp
  · rfl

@[simp] theorem count_one : count 1 = 1 := by
  rw [count_div_two]
  simp

@[simp] theorem count_bool (b : Bool) : count b.toNat = b.toNat := by
  cases b <;> simp

@[simp] theorem count_two_mul_add (n : Nat) (b : Bool) :
    count (2 * n + b.toNat) = count n + b.toNat := by
  rw [count_div_two]
  have hb := b.toNat_lt
  rw [show (2 * n + b.toNat) / 2 = n by omega,
    show (2 * n + b.toNat) % 2 = b.toNat by omega]

theorem count_le (n : Nat) : count n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n; simp
    · rw [count_div_two]
      have := ih (n / 2) (Nat.div_lt_self (by omega) (by decide))
      omega

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

theorem land_split_byte :
    v &&& m = (v % 256 &&& m % 256) + 256 * (v / 256 &&& m / 256) :=
  land_split (s := 8)

theorem land_split' {lo hi lo' hi' : Nat} (hlo : lo < 256) (hlo' : lo' < 256) :
    (lo + 256 * hi) &&& (lo' + 256 * hi') = (lo &&& lo') + 256 * (hi &&& hi') := by
  rw [land_split_byte]
  rw [show (lo + 256 * hi) % 256 = lo by omega,
    show (lo + 256 * hi) / 256 = hi by omega,
    show (lo' + 256 * hi') % 256 = lo' by omega,
    show (lo' + 256 * hi') / 256 = hi' by omega]

theorem shiftLeft_land_shiftRight :
    ((v >>> s) &&& m) <<< s = v &&& (m <<< s) :=
  Nat.eq_of_testBit_eq fun j ↦ by
    by_cases h : s ≤ j
    · simp [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, h,
        Nat.add_sub_cancel' h]
    · simp [Nat.testBit_shiftLeft, Nat.testBit_and, h]

theorem land_15 : v &&& 15 = v % 16 := Nat.and_two_pow_sub_one_eq_mod v 4

theorem land_255 : v &&& 255 = v % 256 := Nat.and_two_pow_sub_one_eq_mod v 8

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

@[simp, grind =] theorem rep_succ : rep b (k + 1) = b + 256 * rep b k := rfl

@[simp, grind =] theorem rep_zero : rep b 0 = 0 := rfl

@[simp, grind =] theorem rep_one : rep b 1 = b := rfl

theorem rep_mod_byte (hb : b < 256) : rep b (k + 1) % 256 = b := by rw [rep_succ]; omega

theorem rep_div_byte (hb : b < 256) : rep b (k + 1) / 256 = rep b k := by rw [rep_succ]; omega

theorem rep_shiftLeft : rep b k <<< s = rep (b <<< s) k := by
  simp only [Nat.shiftLeft_eq]
  induction k with
  | zero => simp
  | succ k ih => simp only [rep_succ, Nat.add_mul, Nat.mul_assoc, ih]

/-- A repeated-byte mask splits at the byte boundary. -/
theorem land_rep_succ (hm : m < 256) :
    v &&& rep m (k + 1) = (v % 256 &&& m) + 256 * (v / 256 &&& rep m k) := by
  rw [land_split_byte, rep_mod_byte hm, rep_div_byte hm]

/-- `rep 1 k` fills `k` bytes with ones. -/
theorem rep_one_mul : 255 * rep 1 k + 1 = 256 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, Nat.pow_succ]; omega

@[simp] theorem stageB_zero : stageB v 0 = 0 := by simp [stageB]
@[simp] theorem stageC_zero : stageC v 0 = 0 := by simp [stageC]

set_option maxRecDepth 8192 in
/-- On a byte the stages stay inside the byte, and the last one holds its set-bit count. -/
theorem byte_pipeline (hv : v < 256) :
    stageA v 1 < 256 ∧ stageB v 1 ≤ 68 ∧ stageB v 1 % 16 ≤ 4 ∧ stageC v 1 ≤ 8 ∧
      stageC v 1 = count v := by
  have h : ∀ v : Fin 256, stageA v 1 < 256 ∧ stageB v 1 ≤ 68 ∧
      stageB v 1 % 16 ≤ 4 ∧ stageC v 1 ≤ 8 ∧ stageC v 1 = count v := by decide +kernel
  exact h ⟨v, hv⟩

theorem stageA_byte_lt (hv : v < 256) : stageA v 1 < 256 := (byte_pipeline hv).1

theorem stageB_byte_le (hv : v < 256) : stageB v 1 ≤ 68 := (byte_pipeline hv).2.1

theorem stageB_byte_mod_16 (hv : v < 256) : stageB v 1 % 16 ≤ 4 := (byte_pipeline hv).2.2.1

theorem stageC_byte_le (hv : v < 256) : stageC v 1 ≤ 8 := (byte_pipeline hv).2.2.2.1

theorem stageC_byte_eq (hv : v < 256) : stageC v 1 = count v := (byte_pipeline hv).2.2.2.2

/-! ## Peeling one byte -/

/-- `f v k`, read at `k + 1` bytes, is the value on the low byte of `v` plus 256 times the value on
the rest of `v`. -/
def IsBytewise (f : Nat → Nat → Nat) : Prop :=
  ∀ v k, f v (k + 1) = f (v % 256) 1 + 256 * f (v / 256) k

section Bytewise
variable {f g : Nat → Nat → Nat}

theorem IsBytewise.eq (hf : IsBytewise f) :
    f v (k + 1) = f (v % 256) 1 + 256 * f (v / 256) k :=
  hf v k

theorem isBytewise_id : IsBytewise fun v _ ↦ v := fun _ _ => (Nat.mod_add_div _ _).symm

theorem IsBytewise.add (hf : IsBytewise f) (hg : IsBytewise g) :
    IsBytewise fun v k ↦ f v k + g v k := by
  intro v k
  dsimp only
  have h1 := hf v k
  have h2 := hg v k
  omega

theorem IsBytewise.sub (hf : IsBytewise f) (hg : IsBytewise g) (hfg : ∀ v k, g v k ≤ f v k) :
    IsBytewise fun v k ↦ f v k - g v k := by
  intro v k
  dsimp only
  have h1 := hf v k
  have h2 := hg v k
  have h3 := hfg (v % 256) 1
  have h4 := hfg (v / 256) k
  omega

theorem IsBytewise.land (hf : IsBytewise f) (hg : IsBytewise g)
    (hf' : ∀ v < 256, f v 1 < 256) (hg' : ∀ v < 256, g v 1 < 256) :
    IsBytewise fun v k ↦ f v k &&& g v k := fun v k ↦ by
  simp only [hf v k, hg v k]
  rw [land_split' (hf' _ (Nat.mod_lt _ (by omega))) (hg' _ (Nat.mod_lt _ (by omega)))]

theorem IsBytewise.of_shiftLeft (h : IsBytewise fun v k ↦ f v k <<< s) : IsBytewise f :=
  fun v k ↦
  Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos s) (by
    have hh := h v k
    simpa only [Nat.shiftLeft_eq, Nat.add_mul, Nat.mul_assoc] using hh)

theorem isBytewise_rep : IsBytewise fun _ k ↦ rep m k := fun v k ↦ by simp

theorem IsBytewise.shiftRight_land_rep (hf : IsBytewise f)
    (hf' : ∀ v < 256, f v 1 < 256) (hms : m <<< s < 256) :
    IsBytewise fun v k ↦ f v k >>> s &&& rep m k := by
  apply IsBytewise.of_shiftLeft (s := s)
  have h := hf.land (isBytewise_rep (m := m <<< s)) hf' (by simp [hms])
  simpa only [shiftLeft_land_shiftRight, rep_shiftLeft] using h

/-- Shifting a value down and masking with a repeated byte acts byte by byte. -/
theorem isBytewise_shiftRight_land_rep (hms : m <<< s < 256) :
    IsBytewise fun v k ↦ v >>> s &&& rep m k :=
  isBytewise_id.shiftRight_land_rep (by simp) hms

theorem isBytewise_stageA : IsBytewise stageA :=
  isBytewise_id.sub (isBytewise_shiftRight_land_rep (by simp))
    (fun _ _ => Nat.le_trans Nat.and_le_left (Nat.shiftRight_le _ _))

theorem isBytewise_stageB : IsBytewise stageB :=
  (isBytewise_stageA.land isBytewise_rep (fun _ ↦ stageA_byte_lt) (by simp)).add
    (isBytewise_stageA.shiftRight_land_rep (fun _ ↦ stageA_byte_lt) (by simp))

theorem stageB_mod_16 (v k : Nat) : stageB v k % 16 ≤ 4 := by
  cases k with
  | zero => simp
  | succ k =>
    have h := stageB_byte_mod_16 (v := v % 256) (Nat.mod_lt _ (by omega))
    rw [isBytewise_stageB.eq]
    omega

/-- The last stage of a two-byte value splits into the stages of its bytes. -/
theorem stageC_byte_split {lo hi : Nat} (hlo : lo ≤ 68) (hhi : hi % 16 ≤ 4) :
    (lo + 256 * hi + ((lo + 256 * hi) >>> 4)) &&& rep 15 (k + 1)
      = ((lo + lo >>> 4) &&& 15) + 256 * ((hi + hi >>> 4) &&& rep 15 k) := by
  rw [land_rep_succ (by decide)]
  simp only [land_15, Nat.shiftRight_eq_div_pow]
  congr 1
  · omega
  · congr 1
    congr 1
    omega

/-- Adding a value to itself shifted right by 4 and masking to 4-bit groups splits at the byte
boundary, given the bounds the previous stage supplies. -/
theorem IsBytewise.add_shiftRight_land_15 (hf : IsBytewise f)
    (hbyte : ∀ v < 256, f v 1 ≤ 68) (hmod : ∀ v k, f v k % 16 ≤ 4) :
    IsBytewise fun v k ↦ (f v k + f v k >>> 4) &&& rep 15 k := fun v k ↦ by
  simpa [hf v k] using stageC_byte_split (hbyte _ (Nat.mod_lt _ (by omega))) (hmod _ _)

theorem isBytewise_stageC : IsBytewise stageC :=
  isBytewise_stageB.add_shiftRight_land_15 (fun _ ↦ stageB_byte_le) stageB_mod_16

end Bytewise

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

def adjacent : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: b :: xs => (a + b) :: adjacent (b :: xs)

def evenDigits : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: _ :: xs => a :: evenDigits xs

def stripe (s : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (2 ^ s - 1) + 2 ^ (s + s) * stripe s k

theorem pack_cons_mod (ha : a < 2 ^ s) : pack s (a :: xs) % 2 ^ s = a := by
  simp only [pack, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem pack_cons_div (ha : a < 2 ^ s) : pack s (a :: xs) / 2 ^ s = pack s xs := by
  simp only [pack, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt ha,
    Nat.zero_add]

theorem pack_adjacent (xs : List Nat) :
    pack s (adjacent xs) = pack s xs + pack s xs.tail := by
  induction xs with
  | nil => simp [adjacent, pack]
  | cons a xs ih =>
    cases xs with
    | nil => simp [adjacent, pack]
    | cons b xs =>
      simp only [adjacent, pack, List.tail_cons] at ih ⊢
      rw [ih, Nat.mul_add]
      omega

theorem adjacent_bound (h : ∀ a ∈ xs, a ≤ s) : ∀ a ∈ adjacent xs, a ≤ s + s := by
  induction xs with
  | nil => simp [adjacent]
  | cons a xs ih =>
    cases xs with
    | nil => simp only [adjacent, List.mem_singleton]; intro b hb; subst b; have := h a (by simp); omega
    | cons b xs =>
      simp only [adjacent, List.mem_cons]
      intro c hc
      rcases hc with rfl | hc
      · have := h a (by simp); have := h b (by simp); omega
      · exact ih (by intro c hc; exact h c (by simp [hc])) _ hc

theorem even_adjacent (xs : List Nat) : evenDigits (adjacent xs) = pairs xs := by
  induction xs using pairs.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih =>
    cases xs with
    | nil => rfl
    | cons c xs => simp only [adjacent, evenDigits, pairs] at ih ⊢; exact congrArg (List.cons (a + b)) ih

theorem pairs_sum (xs : List Nat) : (pairs xs).sum = xs.sum := by
  induction xs using pairs.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b xs ih => simp only [pairs, List.sum_cons, ih, Nat.add_assoc]

theorem pairs_length (h : xs.length = 2 * k) : (pairs xs).length = k := by
  induction k generalizing xs with
  | zero => cases xs with
    | nil => rfl
    | cons a xs => simp at h
  | succ k ih =>
    cases xs with
    | nil => simp at h
    | cons a xs => cases xs with
      | nil => simp at h; omega
      | cons b xs => simp only [List.length_cons] at h; simp only [pairs, List.length_cons]; rw [ih (xs := xs) (by omega)]

theorem pairs_bound (h : ∀ a ∈ xs, a ≤ s) : ∀ a ∈ pairs xs, a ≤ s + s := by
  induction xs using pairs.induct with
  | case1 => simp [pairs]
  | case2 a => simp only [pairs, List.mem_singleton]; intro b hb; subst b; have := h a (by simp); omega
  | case3 a b xs ih =>
    simp only [pairs, List.mem_cons]
    intro c hc
    rcases hc with rfl | hc
    · have := h a (by simp); have := h b (by simp); omega
    · exact ih (by intro c hc; exact h c (by simp [hc])) _ hc


theorem land_parts (ha : a < 2 ^ s) (hb : b < 2 ^ s) :
    (a + 2 ^ s * c) &&& (b + 2 ^ s * d) = (a &&& b) + 2 ^ s * (c &&& d) := by
  rw [land_split (s := s)]
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt ha,
    Nat.div_eq_of_lt hb, Nat.zero_add]

theorem adjacent_length (xs : List Nat) : (adjacent xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases xs with
    | nil => rfl
    | cons b xs => simpa [adjacent] using congrArg Nat.succ ih

theorem pack_land_stripe (hlen : xs.length = 2 * k) (h : ∀ a ∈ xs, a < 2 ^ s) :
    pack s xs &&& stripe s k = pack (s + s) (evenDigits xs) := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [pack, stripe, evenDigits]
    | cons a xs => simp at hlen
  | succ k ih =>
    cases xs with
    | nil => simp at hlen
    | cons a xs => cases xs with
      | nil => simp at hlen; omega
      | cons b xs =>
        have ha := h a (by simp)
        have hb := h b (by simp)
        have hx : ∀ c ∈ xs, c < 2 ^ s := by intro c hc; exact h c (by simp [hc])
        have hl : xs.length = 2 * k := by simp only [List.length_cons] at hlen; omega
        have hp := Nat.two_pow_pos s
        have hlo : a + 2 ^ s * b < 2 ^ (s + s) := by
          rw [Nat.pow_add]
          have hh := Nat.mul_le_mul_left (2 ^ s) hb
          simp only [Nat.mul_succ] at hh
          omega
        have hm : 2 ^ s - 1 < 2 ^ (s + s) := by
          have := Nat.pow_le_pow_right (by decide : 0 < 2) (show s ≤ s + s by omega)
          omega
        simp only [pack, stripe, evenDigits]
        rw [show a + 2 ^ s * (b + 2 ^ s * pack s xs) = (a + 2 ^ s * b) + 2 ^ (s + s) * pack s xs by
          simp [Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]]
        rw [land_parts hlo hm, ih hl hx, Nat.and_two_pow_sub_one_eq_mod,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

/-- Adding the shifted lanes cannot carry: every pair sums to less than the lane base.
The alternating mask keeps exactly the sums of disjoint pairs. -/
theorem pack_merge (hlen : xs.length = 2 * k) (h : ∀ a ∈ xs, a ≤ s)
    (hs : s + s < 2 ^ s) :
    (pack s xs + pack s xs / 2 ^ s) &&& stripe s k = pack (s + s) (pairs xs) := by
  have ht : pack s xs / 2 ^ s = pack s xs.tail := by
    cases xs with
    | nil => simp [pack]
    | cons a xs => exact pack_cons_div (by have := h a (by simp); omega)
  rw [ht, ← pack_adjacent, pack_land_stripe (by rw [adjacent_length]; exact hlen)
    (by intro a ha; have := adjacent_bound h a ha; omega), even_adjacent]

theorem stripe_mul (s k : Nat) :
    (2 ^ s + 1) * stripe s k + 1 = 2 ^ ((s + s) * k) := by
  induction k with
  | zero => simp [stripe]
  | succ k ih =>
    have hp := Nat.two_pow_pos s
    have hc : (2 ^ s + 1) * (2 ^ s - 1) + 1 = 2 ^ (s + s) := by
      have hh := Nat.mul_le_mul_left (2 ^ s) (show 1 ≤ 2 ^ s by omega)
      simp only [Nat.mul_one] at hh
      rw [Nat.mul_sub, Nat.mul_one, Nat.add_mul, Nat.one_mul, Nat.pow_add]
      omega
    rw [stripe]
    calc
      (2 ^ s + 1) * ((2 ^ s - 1) + 2 ^ (s + s) * stripe s k) + 1 =
          ((2 ^ s + 1) * (2 ^ s - 1) + 1) + 2 ^ (s + s) * ((2 ^ s + 1) * stripe s k) := by
        rw [Nat.mul_add]; simp only [Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm]
      _ = 2 ^ (s + s) * ((2 ^ s + 1) * stripe s k + 1) := by rw [hc, Nat.mul_add, Nat.mul_one]; omega
      _ = 2 ^ (s + s) * 2 ^ ((s + s) * k) := by rw [ih]
      _ = 2 ^ ((s + s) * (k + 1)) := by simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add]; simp only [Nat.mul_assoc, Nat.mul_comm]

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
  have h3 : (255 * rep 1 k) / 3 = rep 85 k := by
    rw [show 255 * rep 1 k = 3 * (85 * rep 1 k) by simp only [← Nat.mul_assoc],
      Nat.mul_div_right _ (by decide), rep_mul 85 k]
  have h5 : (255 * rep 1 k) / 5 = rep 51 k := by
    rw [show 255 * rep 1 k = 5 * (51 * rep 1 k) by simp only [← Nat.mul_assoc],
      Nat.mul_div_right _ (by decide), rep_mul 51 k]
  have h17 : (255 * rep 1 k) / 17 = rep 15 k := by
    rw [show 255 * rep 1 k = 17 * (15 * rep 1 k) by simp only [← Nat.mul_assoc],
      Nat.mul_div_right _ (by decide), rep_mul 15 k]
  change (255 * rep 1 k).div 3 = rep 85 k at h3
  change (255 * rep 1 k).div 5 = rep 51 k at h5
  change (255 * rep 1 k).div 17 = rep 15 k at h17
  simp only [bytes, hh]
  rw [h3, h5, h17]
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
    intro a ha
    simp only [byteDigits, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact count_le_of_lt_two_pow (Nat.mod_lt _ (by decide))
    · exact ih _ a ha

theorem byteDigits_pack (n k : Nat) : pack 8 (byteDigits n k) = stageC n k := by
  induction k generalizing n with
  | zero => simp [byteDigits, pack]
  | succ k ih =>
    simp only [byteDigits, pack, ih]
    rw [isBytewise_stageC.eq, stageC_byte_eq (Nat.mod_lt _ (by decide))]

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
    have ha := h a (by simp)
    have hh := ih (by intro b hb; exact h b (by simp [hb]))
    simp only [List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem lane_bound (hs : 8 ≤ s) : s + s < 2 ^ s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 8 + (t + 1) = (8 + t) + 1 by omega, Nat.pow_succ]
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
        have hw : s * 2 ^ (k + 1) = (s + s) * 2 ^ k := by simp only [Nat.pow_succ, Nat.add_mul, ← Nat.mul_assoc]; omega
        rw [hw, ← stripe_eq, Nat.shiftRight_eq_div_pow,
          pack_merge (by rw [hlen, Nat.pow_succ, Nat.mul_comm]) hb (lane_bound hs)]
        apply Eq.trans (ih (k := k) (s := s + s) (xs := pairs xs) (by omega) (pairs_length (by rw [hlen, Nat.pow_succ, Nat.mul_comm]))
          (pairs_bound hb) (by omega))
        exact pairs_sum xs


theorem wide_eq (hn : n < 2 ^ (8 * 2 ^ k)) : wide n (8 * 2 ^ k) = count n := by
  change fold (8 * 2 ^ k) (8 * 2 ^ k) ((1 <<< (8 * 2 ^ k)) - 1) 8 (bytes n ((1 <<< (8 * 2 ^ k)) - 1)) = count n
  rw [Nat.one_shiftLeft, bytes_eq, ← byteDigits_pack]
  rw [fold_eq (by have := Nat.lt_two_pow_self (n := k); omega)
    (byteDigits_length n (2 ^ k)) (byteDigits_bound n (2 ^ k)) (by decide), byteDigits_sum hn]

theorem grow_eq (hn : n < 2 ^ (8 * 2 ^ k + fuel)) : grow fuel n (8 * 2 ^ k) = count n := by
  induction fuel generalizing k with
  | zero => exact wide_eq (by simpa using hn)
  | succ fuel ih =>
    change Bool.rec (motive := fun _ => Nat)
      (grow fuel n ((8 * 2 ^ k) + (8 * 2 ^ k))) (wide n (8 * 2 ^ k)) ((n >>> (8 * 2 ^ k)).beq 0) = count n
    cases h : (n >>> (8 * 2 ^ k)).beq 0 with
    | true =>
      dsimp only
      have hh : n / 2 ^ (8 * 2 ^ k) = 0 := by simpa only [Nat.beq_eq, Nat.shiftRight_eq_div_pow] using h
      exact wide_eq (Nat.lt_of_div_eq_zero (Nat.two_pow_pos _) hh)
    | false =>
      dsimp only
      rw [show 8 * 2 ^ k + 8 * 2 ^ k = 8 * 2 ^ (k + 1) by rw [Nat.pow_succ]; omega]
      apply ih
      have hp := Nat.two_pow_pos k
      have hm : 8 * 2 ^ k + (fuel + 1) ≤ 8 * 2 ^ (k + 1) + fuel := by rw [Nat.pow_succ]; omega
      exact Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hm)

set_option exponentiation.threshold 65536

theorem small_eq (hn : n < 2 ^ 64) : small n = count n := by
  change wide n (8 * 2 ^ 3) = count n
  exact wide_eq hn

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
  cases h64 : (n.shiftRight 64).beq 0 with
  | true => exact small_eq (bound _ h64)
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

private theorem popcount_eq (n : Nat) : popcount n = popcount.count n :=
  popcount.count_eq n

@[simp] public theorem popcount_zero : popcount 0 = 0 := by
  simpa only [popcount_eq] using popcount.count_zero

public theorem popcount_div_two (n : Nat) : popcount n = popcount (n / 2) + n % 2 := by
  simpa only [popcount_eq] using popcount.count_div_two n

@[simp] public theorem popcount_one : popcount 1 = 1 := by
  simpa only [popcount_eq] using popcount.count_one

@[simp] public theorem popcount_bool (b : Bool) : popcount b.toNat = b.toNat := by
  simpa only [popcount_eq] using popcount.count_bool b

@[simp] public theorem popcount_two_mul_add (n : Nat) (b : Bool) :
    popcount (2 * n + b.toNat) = popcount n + b.toNat := by
  simpa only [popcount_eq] using popcount.count_two_mul_add n b

public theorem popcount_le (n : Nat) : popcount n ≤ n := by
  simpa only [popcount_eq] using popcount.count_le n

/-- Splitting at any binary digit adds the counts of the two parts. -/
public theorem popcount_mul_two_pow_add (a k b : Nat) (hb : b < 2 ^ k) :
    popcount (a * 2 ^ k + b) = popcount a + popcount b := by
  simpa only [popcount_eq] using popcount.count_mul_two_pow_add a k b hb

public theorem popcount_mod_add_div (n k : Nat) :
    popcount (n % 2 ^ k) + popcount (n / 2 ^ k) = popcount n := by
  simpa only [popcount_eq] using popcount.count_mod_add_div n k

public theorem popcount_le_of_lt_two_pow {n k : Nat} (h : n < 2 ^ k) : popcount n ≤ k := by
  simpa only [popcount_eq] using popcount.count_le_of_lt_two_pow h

end Nat
