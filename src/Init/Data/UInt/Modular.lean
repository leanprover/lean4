/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.UInt.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.ByCases
import Init.Omega
import Init.WFTactics

@[expose] public section

namespace UInt64

/--
Multiplies two 64-bit unsigned integers and reduces the result modulo `modulus` without losing the
high half of the product. When `modulus` is `0`, the result is the wrapped product.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_mul_mod", implicit_reducible]
def mulMod (a b modulus : UInt64) : UInt64 :=
  .ofNat (a.toNat * b.toNat % modulus.toNat)

/--
Raises a 64-bit unsigned integer to a natural-number power modulo `modulus`, using
exponentiation by squaring. When `modulus` is `0`, the result is the wrapped power.
-/
def powMod (base : UInt64) (exponent : Nat) (modulus : UInt64) : UInt64 :=
  if exponent = 0 then
    1 % modulus
  else
    let result := powMod (mulMod base base modulus) (exponent / 2) modulus
    if exponent % 2 = 1 then mulMod result base modulus else result
termination_by exponent
decreasing_by omega

/--
Returns the multiplicative inverse of `a` modulo `modulus`, or `none` if the inverse does not
exist. When `modulus` is `0`, the result is `none`. For a nonzero modulus, an inverse exists exactly
when `a` and `modulus` are coprime.
-/
def invMod? (a modulus : UInt64) : Option UInt64 :=
  if modulus = 0 then
    none
  else
    let rec go (oldR r oldS s : Nat) : Nat × Nat :=
      if _h : r = 0 then
        (oldR, oldS)
      else
        let quotient := oldR / r
        let product := quotient * s % modulus.toNat
        let nextS := if product ≤ oldS then oldS - product else modulus.toNat - (product - oldS)
        go r (oldR % r) s nextS
    termination_by r
    decreasing_by exact Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _h)
    let (gcd, inverse) := go (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0
    if gcd = 1 then some (.ofNat inverse) else none

/-! ### Runtime implementations

`powMod` and `invMod?` are defined above using natural-number arithmetic, which allocates for every
intermediate product. The definitions below keep the modular arithmetic in machine words, so a
`Nat` exponent costs one division per 64 bits rather than one per bit. They are installed with
`@[csimp]`, so the compiled behaviour is proved equal to the definitions above.
-/

/--
Multiplies `result` by `base ^ exponent` modulo `modulus`, consuming the bits of the word-sized
`exponent` from the least significant end. `result` is returned unchanged when `exponent` is `0`,
so the accumulator passed in must already be reduced modulo `modulus`.
-/
def powModWord (base exponent modulus result : UInt64) : UInt64 :=
  if _h : exponent = 0 then result
  else
    let result := if exponent % 2 = 1 then mulMod result base modulus else result
    let exponent' := exponent / 2
    if exponent' = 0 then result
    else powModWord (mulMod base base modulus) exponent' modulus result
termination_by exponent.toNat
decreasing_by
  simp only [UInt64.toNat_div]
  change exponent.toNat / 2 < exponent.toNat
  have : exponent.toNat ≠ 0 := by simpa [← UInt64.toNat_inj] using _h
  omega

/--
Performs `steps` squaring steps, consuming that many bits of `exponent`. Returns the repeatedly
squared base alongside the accumulated result. Neither is reduced modulo `modulus` unless a step
runs, so `steps = 0` returns both arguments unchanged and the accumulator passed in must already
be reduced.
-/
def powModChunk (modulus : UInt64) : Nat → UInt64 → UInt64 → UInt64 → UInt64 × UInt64
  | 0, base, _, result => (base, result)
  | n + 1, base, exponent, result =>
    let result := if exponent % 2 = 1 then mulMod result base modulus else result
    powModChunk modulus n (mulMod base base modulus) (exponent / 2) result

/--
Efficient implementation of `UInt64.powMod`. A `Nat` exponent is consumed 64 bits at a time, so
arbitrarily large exponents only pay for one `Nat` division per word rather than per bit.
-/
def powModImpl (base : UInt64) (exponent : Nat) (modulus : UInt64) : UInt64 :=
  if modulus = 1 then 0 else go base exponent 1
where
  go (base : UInt64) (exponent : Nat) (result : UInt64) : UInt64 :=
    if exponent < 2 ^ 64 then powModWord base exponent.toUInt64 modulus result
    else
      let (base, result) := powModChunk modulus 64 base exponent.toUInt64 result
      go base (exponent / 2 ^ 64) result
  termination_by exponent
  decreasing_by omega

/-- Efficient implementation of `UInt64.invMod?`, using a word-sized extended Euclidean loop. -/
def invModImpl (a modulus : UInt64) : Option UInt64 :=
  if modulus = 0 then none else go (a % modulus) modulus (1 % modulus) 0
where
  go (oldR r oldS s : UInt64) : Option UInt64 :=
    if _h : r = 0 then
      if oldR = 1 then some oldS else none
    else
      let product := mulMod (oldR / r) s modulus
      let nextS := if product ≤ oldS then oldS - product else modulus - (product - oldS)
      go r (oldR % r) s nextS
  termination_by r.toNat
  decreasing_by
    apply UInt64.mod_lt
    change 0 < r.toNat
    have : r.toNat ≠ 0 := by simpa [← UInt64.toNat_inj] using _h
    omega

/-! ### Correctness of the runtime implementations -/

/--
The modulus the operations actually reduce by. A `modulus` of `0` means "do not reduce", which for
a 64-bit result is reduction modulo `2 ^ 64`.
-/
private def wrapMod (modulus : UInt64) : Nat := if modulus = 0 then 2 ^ 64 else modulus.toNat

private theorem toNat_ne_zero {modulus : UInt64} (h : modulus ≠ 0) : modulus.toNat ≠ 0 := by
  simpa [← UInt64.toNat_inj] using h

private theorem wrapMod_pos (modulus : UInt64) : 0 < wrapMod modulus := by
  unfold wrapMod; split
  · exact Nat.two_pow_pos 64
  · rename_i h; have := toNat_ne_zero h; omega

private theorem mod_wrapMod (x : Nat) (modulus : UInt64) :
    x % modulus.toNat % 2 ^ 64 = x % wrapMod modulus := by
  unfold wrapMod; split
  · rename_i h; subst h; simp
  · rename_i h
    have h0 := toNat_ne_zero h
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (Nat.le_of_lt modulus.toNat_lt))

private theorem toNat_mulMod' (a b modulus : UInt64) :
    (mulMod a b modulus).toNat = a.toNat * b.toNat % wrapMod modulus := by
  rw [← mod_wrapMod]
  simp [mulMod, UInt64.toNat_ofNat']

@[simp] theorem toNat_mulMod {a b modulus : UInt64} (h : modulus ≠ 0) :
    (mulMod a b modulus).toNat = a.toNat * b.toNat % modulus.toNat := by
  rw [toNat_mulMod', wrapMod]
  simp only [h, ↓reduceIte]

theorem mulMod_lt {a b modulus : UInt64} (h : modulus ≠ 0) : mulMod a b modulus < modulus := by
  rw [UInt64.lt_iff_toNat_lt, toNat_mulMod h]
  exact Nat.mod_lt _ (Nat.zero_lt_of_ne_zero (toNat_ne_zero h))

private theorem div_two_lt_of_lt_two_mul {m k : Nat} (h : m < 2 * k) : m / 2 < k := by
  omega

private theorem mul_pow_mod (a b k n : Nat) : a * (b % n) ^ k % n = a * b ^ k % n := by
  rw [Nat.mul_mod a ((b % n) ^ k) n, ← Nat.pow_mod, ← Nat.mul_mod]

private theorem mul_pow_pow_mod (a b c w k n : Nat) (h : c % n = b ^ w % n) :
    a * c ^ k % n = a * b ^ (w * k) % n := by
  rw [Nat.mul_mod, Nat.pow_mod, h, ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.mul_mod]

private theorem toNat_bit (e : UInt64) : (e % 2 = (1 : UInt64)) ↔ e.toNat % 2 = 1 := by
  rw [← UInt64.toNat_inj, UInt64.toNat_mod]
  rfl

private theorem toNat_condMul (base result modulus e : UInt64)
    (hres : result.toNat < wrapMod modulus) :
    (if e % 2 = 1 then mulMod result base modulus else result).toNat
      = result.toNat * base.toNat ^ (e.toNat % 2) % wrapMod modulus := by
  by_cases h : e % 2 = (1 : UInt64)
  · have h' : e.toNat % 2 = 1 := (toNat_bit e).mp h
    simp only [h, ↓reduceIte, h', Nat.pow_one]
    exact toNat_mulMod' _ _ _
  · have h' : e.toNat % 2 ≠ 1 := fun hc => h ((toNat_bit e).mpr hc)
    have h0 : e.toNat % 2 = 0 := by omega
    simp only [h, ↓reduceIte, h0, Nat.pow_zero, Nat.mul_one]
    exact (Nat.mod_eq_of_lt hres).symm

private theorem toNat_powMod' (base : UInt64) (e : Nat) (modulus : UInt64) :
    (powMod base e modulus).toNat = base.toNat ^ e % wrapMod modulus := by
  induction base, e using powMod.induct (modulus := modulus) with
  | case1 base =>
    have h1 : 1 % modulus.toNat < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.mod_le 1 modulus.toNat) (by omega)
    rw [powMod]
    simp only [↓reduceIte, Nat.pow_zero]
    rw [UInt64.toNat_mod, ← mod_wrapMod, show (1 : UInt64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt h1]
  | case2 base e he hodd ih =>
    have he2 : 2 * (e / 2) + 1 = e := by omega
    rw [powMod]
    simp only [he, hodd, ↓reduceIte]
    rw [toNat_mulMod', ih, toNat_mulMod', ← Nat.pow_mod, Nat.mod_mul_mod, ← Nat.pow_two,
      ← Nat.pow_mul, ← Nat.pow_succ, Nat.succ_eq_add_one, he2]
  | case3 base e he heven ih =>
    have he2 : 2 * (e / 2) = e := by omega
    rw [powMod]
    simp only [he, heven, ↓reduceIte]
    rw [ih, toNat_mulMod', ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul, he2]

@[simp] theorem toNat_powMod {base : UInt64} {e : Nat} {modulus : UInt64} (h : modulus ≠ 0) :
    (powMod base e modulus).toNat = base.toNat ^ e % modulus.toNat := by
  rw [toNat_powMod', wrapMod]
  simp only [h, ↓reduceIte]

private theorem toNat_powModWord (base e modulus result : UInt64) :
    result.toNat < wrapMod modulus →
    (powModWord base e modulus result).toNat
      = result.toNat * base.toNat ^ e.toNat % wrapMod modulus := by
  induction base, e, result using powModWord.induct (modulus := modulus) with
  | case1 base result =>
    intro hres
    rw [powModWord]
    simp only [↓reduceDIte, show (0 : UInt64).toNat = 0 from rfl, Nat.pow_zero, Nat.mul_one]
    exact (Nat.mod_eq_of_lt hres).symm
  | case2 base e result he e' he' =>
    intro hres
    simp only [e'] at he'
    have hlt : e.toNat < 2 := by
      have : e.toNat / 2 = 0 := by simpa [← UInt64.toNat_inj] using he'
      omega
    rw [powModWord]
    simp only [he, ↓reduceDIte, he', ↓reduceIte]
    rw [toNat_condMul base result modulus e hres, show e.toNat % 2 = e.toNat by omega]
  | case3 base e result he result' e' he' ih =>
    intro hres
    simp only [e'] at he'
    simp only [result', e', dite_eq_ite] at ih
    have hres' : (if e % 2 = 1 then mulMod result base modulus else result).toNat
        < wrapMod modulus := by
      rw [toNat_condMul base result modulus e hres]
      exact Nat.mod_lt _ (wrapMod_pos modulus)
    have hsplit : e.toNat % 2 + 2 * (e.toNat / 2) = e.toNat := by omega
    rw [powModWord]
    simp only [he, ↓reduceDIte, he', ↓reduceIte]
    rw [ih hres', toNat_condMul base result modulus e hres, toNat_mulMod', Nat.mod_mul_mod,
      mul_pow_mod, ← Nat.pow_two, ← Nat.pow_mul, UInt64.toNat_div,
      show (2 : UInt64).toNat = 2 from rfl, Nat.mul_assoc, ← Nat.pow_add, hsplit]

private theorem toNat_powModChunk_fst (modulus : UInt64) (n : Nat) (base e result : UInt64) :
    (powModChunk modulus n base e result).1.toNat % wrapMod modulus
      = base.toNat ^ 2 ^ n % wrapMod modulus := by
  induction n generalizing base e result with
  | zero => simp [powModChunk]
  | succ n ih =>
    rw [powModChunk, ih, toNat_mulMod', ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul,
      ← Nat.pow_succ']

private theorem toNat_powModChunk_snd (modulus : UInt64) (n : Nat) (base e result : UInt64)
    (he : e.toNat < 2 ^ n) (hres : result.toNat < wrapMod modulus) :
    (powModChunk modulus n base e result).2.toNat
      = result.toNat * base.toNat ^ e.toNat % wrapMod modulus := by
  induction n generalizing base e result with
  | zero =>
    have : e.toNat = 0 := by simpa using he
    simp only [powModChunk, this, Nat.pow_zero, Nat.mul_one]
    exact (Nat.mod_eq_of_lt hres).symm
  | succ n ih =>
    have hres' : (if e % 2 = 1 then mulMod result base modulus else result).toNat
        < wrapMod modulus := by
      rw [toNat_condMul base result modulus e hres]
      exact Nat.mod_lt _ (wrapMod_pos modulus)
    have hdiv : (e / 2).toNat < 2 ^ n := by
      rw [UInt64.toNat_div, show (2 : UInt64).toNat = 2 from rfl]
      exact div_two_lt_of_lt_two_mul (by rw [← Nat.pow_succ']; exact he)
    have hsplit := Nat.mod_add_div e.toNat 2
    rw [powModChunk, ih _ _ _ hdiv hres', toNat_condMul base result modulus e hres,
      toNat_mulMod', Nat.mod_mul_mod, mul_pow_mod, ← Nat.pow_two, ← Nat.pow_mul,
      UInt64.toNat_div, show (2 : UInt64).toNat = 2 from rfl, Nat.mul_assoc, ← Nat.pow_add,
      hsplit]

private theorem toNat_powModImpl_go (modulus base : UInt64) (e : Nat) (result : UInt64) :
    result.toNat < wrapMod modulus →
    (powModImpl.go modulus base e result).toNat
      = result.toNat * base.toNat ^ e % wrapMod modulus := by
  induction base, e, result using powModImpl.go.induct (modulus := modulus) with
  | case1 base e result he =>
    intro hres
    rw [powModImpl.go]
    simp only [he, ↓reduceIte]
    rw [toNat_powModWord _ _ _ _ hres, Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt he]
  | case2 base e result he b' r' hchunk ih =>
    intro hres
    have hlo : (e.toUInt64).toNat = e % 2 ^ 64 := by rw [Nat.toUInt64, UInt64.toNat_ofNat']
    have hlolt : (e.toUInt64).toNat < 2 ^ 64 := by rw [hlo]; exact Nat.mod_lt _ (by omega)
    have hr' : r'.toNat = result.toNat * base.toNat ^ (e % 2 ^ 64) % wrapMod modulus := by
      have := toNat_powModChunk_snd modulus 64 base e.toUInt64 result hlolt hres
      rw [hchunk] at this
      rw [this, hlo]
    have hb' := toNat_powModChunk_fst modulus 64 base e.toUInt64 result
    rw [hchunk] at hb'
    have hres' : r'.toNat < wrapMod modulus := by
      rw [hr']; exact Nat.mod_lt _ (wrapMod_pos modulus)
    rw [powModImpl.go]
    simp only [he, ↓reduceIte, hchunk]
    rw [ih hres', hr', Nat.mod_mul_mod, mul_pow_pow_mod _ _ _ _ _ _ hb', Nat.mul_assoc,
      ← Nat.pow_add, Nat.mod_add_div]

@[csimp] theorem powMod_eq_powModImpl : @powMod = @powModImpl := by
  funext base e modulus
  by_cases hm : modulus = 1
  · subst hm
    rw [powModImpl]
    simp only [↓reduceIte]
    rw [← UInt64.toNat_inj, toNat_powMod', show wrapMod 1 = 1 from by simp [wrapMod],
      Nat.mod_one]
    rfl
  · have hM : 1 < wrapMod modulus := by
      unfold wrapMod; split
      · exact Nat.one_lt_two_pow (by omega)
      · rename_i h
        have h0 := toNat_ne_zero h
        have h1 : modulus.toNat ≠ 1 := by simpa [← UInt64.toNat_inj] using hm
        omega
    rw [powModImpl]
    simp only [hm, ↓reduceIte]
    rw [← UInt64.toNat_inj, toNat_powModImpl_go _ _ _ _ (by simpa using hM), toNat_powMod']
    simp

private theorem toNat_condSub {a b modulus : UInt64} (hb : b < modulus) :
    (if b ≤ a then a - b else modulus - (b - a)).toNat
      = if b.toNat ≤ a.toNat then a.toNat - b.toNat
        else modulus.toNat - (b.toNat - a.toNat) := by
  have hbm : b.toNat < modulus.toNat := UInt64.lt_iff_toNat_lt.mp hb
  by_cases h : b ≤ a
  · have h' : b.toNat ≤ a.toNat := UInt64.le_iff_toNat_le.mp h
    simp only [h, h', ↓reduceIte]
    exact UInt64.toNat_sub_of_le _ _ h
  · have h' : ¬ b.toNat ≤ a.toNat := fun hc => h (UInt64.le_iff_toNat_le.mpr hc)
    have hab : a ≤ b := UInt64.le_iff_toNat_le.mpr (by omega)
    have hsub : b - a ≤ modulus := UInt64.le_iff_toNat_le.mpr (by
      rw [UInt64.toNat_sub_of_le _ _ hab]; omega)
    simp only [h, h', ↓reduceIte]
    rw [UInt64.toNat_sub_of_le _ _ hsub, UInt64.toNat_sub_of_le _ _ hab]

private theorem invModImpl_go_eq (modulus : UInt64) (hm : modulus ≠ 0) (oldR r oldS s : UInt64) :
    invModImpl.go modulus oldR r oldS s =
      (if (invMod?.go modulus oldR.toNat r.toNat oldS.toNat s.toNat).1 = 1 then
        some (UInt64.ofNat (invMod?.go modulus oldR.toNat r.toNat oldS.toNat s.toNat).2)
      else none) := by
  induction oldR, r, oldS, s using invModImpl.go.induct (modulus := modulus) with
  | case1 oldS s =>
    rw [invModImpl.go, invMod?.go]
    simp
  | case2 oldR oldS s h =>
    rw [invModImpl.go, invMod?.go]
    simp [h, show oldR.toNat ≠ 1 by simpa [← UInt64.toNat_inj] using h]
  | case3 oldR r oldS s hr product nextS ih =>
    have hr' : ¬ r.toNat = 0 := by simpa [← UInt64.toNat_inj] using hr
    simp only [product, nextS, dite_eq_ite] at ih
    have hstep : invMod?.go modulus oldR.toNat r.toNat oldS.toNat s.toNat
        = invMod?.go modulus r.toNat (oldR % r).toNat s.toNat
            (if mulMod (oldR / r) s modulus ≤ oldS then oldS - mulMod (oldR / r) s modulus
             else modulus - (mulMod (oldR / r) s modulus - oldS)).toNat := by
      rw [invMod?.go]
      simp only [hr', ↓reduceDIte]
      rw [UInt64.toNat_mod, toNat_condSub (mulMod_lt hm), toNat_mulMod hm, UInt64.toNat_div]
    rw [invModImpl.go]
    simp only [hr, ↓reduceDIte]
    rw [ih, hstep]

@[csimp] theorem invMod?_eq_invModImpl : @invMod? = @invModImpl := by
  funext a modulus
  by_cases hm : modulus = 0
  · simp [invMod?, invModImpl, hm]
  · rw [invMod?, invModImpl]
    simp only [hm, ↓reduceIte]
    rw [invModImpl_go_eq modulus hm]
    simp [UInt64.toNat_mod]

end UInt64
