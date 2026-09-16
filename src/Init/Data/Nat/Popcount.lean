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
import Init.Data.Int.Pow -- Used by omega when normalizing powers.
import Init.ByCases
import Init.RCases
import Init.Omega
import Init.WFTactics

/-!
# Population count

The kernel-reducible implementation counts 248-bit chunks using shifts, masks, and multiplication.
The bytewise algorithm and proof follow Bhavik Mehta's `PrimeCert.PopCount`.
-/
namespace Nat
namespace popcount

/-- Count a chunk of at most 248 bits. Each byte is replaced by its bit count, then
multiplication adds these counts into the highest byte. The sum is at most 248. -/
@[expose, implicit_reducible] public def word (v : Nat) : Nat :=
  let a := v.sub
    ((v.shiftRight 1).land 0x55555555555555555555555555555555555555555555555555555555555555)
  let b := (a.land 0x33333333333333333333333333333333333333333333333333333333333333).add
    ((a.shiftRight 2).land 0x33333333333333333333333333333333333333333333333333333333333333)
  let c := (b.add (b.shiftRight 4)).land
    0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
  ((c.mul 0x01010101010101010101010101010101010101010101010101010101010101).shiftRight 240).land 255

/-- Count chunks using structural recursion. The result is correct when `n < fuel`. -/
@[expose, implicit_reducible] public noncomputable def loop : Nat → Nat → Nat :=
  Nat.rec (fun _ => 0) (fun _ rec n =>
    (n.ble 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff).rec
      ((word (n.land 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)).add
        (rec (n.shiftRight 248)))
      (word n))

end popcount

/-- The number of set bits in the binary representation of a natural number.
Kernel reduction counts 248-bit chunks using existing natural-number arithmetic.
The compiled implementation scans machine limbs. -/
@[expose, implicit_reducible, extern "lean_nat_popcount"] public def popcount (n : @& Nat) : Nat :=
  popcount.loop n.succ n

namespace popcount

/-- Binary specification used to prove the chunk algorithm. -/
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

`rep b k` is the `k`-byte constant repeating the byte `b`. The masks of `word` are `rep 85 31`,
`rep 51 31` and `rep 15 31`, and its multiplier is `rep 1 31`. -/

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

/-- The top byte of a repeated-byte constant. -/
theorem rep_succ_top : rep b (k + 1) = rep b k + 256 ^ k * b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [rep_succ, ih, Nat.mul_add, ← Nat.add_assoc, ← rep_succ, Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm 256, ih]

/-- A repeated-byte constant fits in its `k` bytes. -/
theorem rep_lt (hb : b < 256) : rep b k < 256 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, Nat.pow_succ]; omega

/-- `rep 1 k` fills `k` bytes with ones. -/
theorem rep_one_mul : 255 * rep 1 k + 1 = 256 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, Nat.pow_succ]; omega

@[simp] theorem stageB_zero : stageB v 0 = 0 := by simp [stageB]
@[simp] theorem stageC_zero : stageC v 0 = 0 := by simp [stageC]

/-- The last stage fits in its `k` bytes. -/
theorem stageC_lt : stageC v k < 256 ^ k :=
  Nat.lt_of_le_of_lt Nat.and_le_right (rep_lt (by omega))

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

/-! Multiplication adds the byte counts into the highest byte. -/
def byteSum : Nat → Nat → Nat
  | _, 0 => 0
  | v, k + 1 => v % 256 + byteSum (v / 256) k

@[simp] theorem byteSum_zero (v : Nat) : byteSum v 0 = 0 := rfl
@[simp] theorem byteSum_succ (v k : Nat) :
    byteSum v (k + 1) = v % 256 + byteSum (v / 256) k := rfl

theorem mul_rep_split (hv : v < 256 ^ (k + 1)) :
    ∃ L T, L ≤ byteSum v (k + 1) * rep 1 k ∧
      v * rep 1 (k + 1) = L + 256 ^ k * (byteSum v (k + 1) + 256 * T) := by
  induction k generalizing v with
  | zero =>
    have hv' : v < 256 := by simpa using hv
    exact ⟨0, 0, by simp, by simp [Nat.mod_eq_of_lt hv']⟩
  | succ k ih =>
    obtain ⟨L, T, hL, hLT⟩ := ih (v := v / 256) (by rw [Nat.pow_succ] at hv; omega)
    have h1 : 256 * rep 1 k ≤ rep 1 (k + 1) := by rw [rep_succ]; omega
    have hw : v = v % 256 + 256 * (v / 256) := (Nat.mod_add_div _ _).symm
    refine ⟨v % 256 * rep 1 (k + 1) + 256 * L, T + v / 256, ?_, ?_⟩
    · have h2 : 256 * L ≤ byteSum (v / 256) (k + 1) * rep 1 (k + 1) := by
        calc
          256 * L ≤ 256 * (byteSum (v / 256) (k + 1) * rep 1 k) :=
            Nat.mul_le_mul_left _ hL
          _ = byteSum (v / 256) (k + 1) * (256 * rep 1 k) := by
            simp only [Nat.mul_left_comm]
          _ ≤ _ := Nat.mul_le_mul_left _ h1
      rw [byteSum_succ, Nat.add_mul]
      omega
    · conv => lhs; rw [hw, Nat.add_mul]
      rw [rep_succ_top (b := 1) (k := k + 1), Nat.mul_one]
      rw [Nat.mul_add (256 * (v / 256)), Nat.mul_assoc 256, hLT]
      simp only [byteSum_succ, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm]

theorem byteSum_mul_rep (hv : v < 256 ^ (k + 1)) (h : byteSum v (k + 1) < 256) :
    v * rep 1 (k + 1) / 256 ^ k % 256 = byteSum v (k + 1) := by
  obtain ⟨L, T, hL, hLT⟩ := mul_rep_split hv
  have h255 : byteSum v (k + 1) * rep 1 k ≤ 255 * rep 1 k :=
    Nat.mul_le_mul_right _ (by omega)
  have hrep := rep_one_mul (k := k)
  have hlt : L < 256 ^ k := by omega
  rw [hLT, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hlt]
  omega

theorem byteSum_stageC (hv : v < 256 ^ k) : byteSum (stageC v k) k = count v := by
  induction k generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    subst v; simp
  | succ k ih =>
    have hb := stageC_byte_le (v := v % 256) (Nat.mod_lt _ (by decide))
    have heq := isBytewise_stageC v k
    have hmod : stageC v (k + 1) % 256 = stageC (v % 256) 1 := by omega
    have hdiv : stageC v (k + 1) / 256 = stageC (v / 256) k := by omega
    rw [byteSum_succ, hmod, hdiv, ih (by rw [Nat.pow_succ] at hv; omega),
      stageC_byte_eq (Nat.mod_lt _ (by decide))]
    exact count_mod_add_div v 8

theorem stageC_mul_rep (hv : v < 256 ^ (k + 1)) (hk : k < 31) :
    stageC v (k + 1) * rep 1 (k + 1) / 256 ^ k % 256 = count v := by
  have hn : count v ≤ 8 * (k + 1) := count_le_of_lt_two_pow (by
    simpa only [Nat.pow_mul] using hv)
  rw [byteSum_mul_rep stageC_lt (by rw [byteSum_stageC hv]; omega), byteSum_stageC hv]

set_option maxRecDepth 8192 in
private theorem word_eq (hv : v < 2 ^ 248) : word v = count v := by
  change (stageC v 31 * rep 1 31) >>> 240 &&& 255 = count v
  rw [Nat.shiftRight_eq_div_pow, land_255]
  exact stageC_mul_rep hv (by decide)

private theorem loop_eq (hf : n < fuel) : loop fuel n = count n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    change Bool.rec (motive := fun _ => Nat)
      (word (n &&& 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) +
        loop fuel (n >>> 248))
      (word n) (n.ble 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) = count n
    rw [show n &&& 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff =
        n % 0x100000000000000000000000000000000000000000000000000000000000000 from
      Nat.and_two_pow_sub_one_eq_mod n 248,
      show n >>> 248 = n / 0x100000000000000000000000000000000000000000000000000000000000000 from
        Nat.shiftRight_eq_div_pow n 248]
    cases h : n.ble 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff with
    | false =>
      dsimp only
      rw [word_eq (Nat.mod_lt _ (by decide)), ih (by
        have hh : ¬ n ≤ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by
          intro hh
          simp [Nat.ble_eq_true_of_le hh] at h
        have hn : 0 < n := by omega
        have hd := Nat.div_lt_self hn
          (show 1 < 0x100000000000000000000000000000000000000000000000000000000000000 by decide)
        omega)]
      exact count_mod_add_div n 248
    | true =>
      dsimp only
      exact word_eq (by have := Nat.le_of_ble_eq_true h; omega)

end popcount

private theorem popcount_eq (n : Nat) : popcount n = popcount.count n :=
  popcount.loop_eq (Nat.lt_succ_self _)

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
