/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.UInt.Basic
public import Init.Data.Nat.Gcd
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

/-! ### Basic properties

Every operation reduces its result modulo `modulus`, except that a `modulus` of `0` means "do not
reduce", which for a 64-bit result is reduction modulo `2 ^ 64`. `wrapMod` names that distinction
so both cases can be handled uniformly.
-/

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
  · exact Nat.pos_of_ne_zero (toNat_ne_zero ‹_›)

private theorem mod_wrapMod (x : Nat) (modulus : UInt64) :
    x % modulus.toNat % 2 ^ 64 = x % wrapMod modulus := by
  by_cases h : modulus = 0
  · simp [wrapMod, h]
  · rw [wrapMod, ite_eq_right h]
    exact Nat.mod_eq_of_lt
      (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (toNat_ne_zero h))) modulus.toNat_lt)

private theorem toNat_mulMod' (a b modulus : UInt64) :
    (mulMod a b modulus).toNat = a.toNat * b.toNat % wrapMod modulus := by
  rw [← mod_wrapMod, mulMod, UInt64.toNat_ofNat']

@[simp] theorem toNat_mulMod {a b modulus : UInt64} (h : modulus ≠ 0) :
    (mulMod a b modulus).toNat = a.toNat * b.toNat % modulus.toNat := by
  rw [toNat_mulMod', wrapMod, ite_eq_right h]

theorem mulMod_lt {a b modulus : UInt64} (h : modulus ≠ 0) : mulMod a b modulus < modulus := by
  rw [UInt64.lt_iff_toNat_lt, toNat_mulMod h]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (toNat_ne_zero h))

@[simp] theorem toNat_mulMod_zero {a b : UInt64} :
    (mulMod a b 0).toNat = a.toNat * b.toNat % 2 ^ 64 :=
  toNat_mulMod' a b 0

private theorem toNat_powMod' (base : UInt64) (e : Nat) (modulus : UInt64) :
    (powMod base e modulus).toNat = base.toNat ^ e % wrapMod modulus := by
  induction base, e using powMod.induct (modulus := modulus) with
  | case1 base =>
    rw [powMod, ite_eq_left rfl, UInt64.toNat_mod, UInt64.toNat_one, Nat.pow_zero, ← mod_wrapMod,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le 1 _) (by decide))]
  | case2 base e he hodd ih =>
    rw [powMod, ite_eq_right he, ite_eq_left hodd, toNat_mulMod', ih, toNat_mulMod', ← Nat.pow_mod,
      Nat.mod_mul_mod, ← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add_one,
      show 2 * (e / 2) + 1 = e by omega]
  | case3 base e he heven ih =>
    rw [powMod, ite_eq_right he, ite_eq_right heven, ih, toNat_mulMod', ← Nat.pow_mod,
      ← Nat.pow_two, ← Nat.pow_mul, show 2 * (e / 2) = e by omega]

@[simp] theorem toNat_powMod {base : UInt64} {e : Nat} {modulus : UInt64} (h : modulus ≠ 0) :
    (powMod base e modulus).toNat = base.toNat ^ e % modulus.toNat := by
  rw [toNat_powMod', wrapMod, ite_eq_right h]

@[simp] theorem toNat_powMod_zero {base : UInt64} {e : Nat} :
    (powMod base e 0).toNat = base.toNat ^ e % 2 ^ 64 :=
  toNat_powMod' base e 0

theorem powMod_lt {base : UInt64} {e : Nat} {modulus : UInt64} (h : modulus ≠ 0) :
    powMod base e modulus < modulus := by
  rw [UInt64.lt_iff_toNat_lt, toNat_powMod h]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (toNat_ne_zero h))

/-! ### Correctness of `invMod?`

`invMod?.go` is the extended Euclidean algorithm carrying a single coefficient sequence. Writing
`a` for the value being inverted, it maintains `oldS * a ≡ oldR` and `s * a ≡ r` modulo `modulus`,
while `Nat.gcd oldR r` stays fixed. At exit `r = 0`, so the first component is the gcd and the
second is a Bézout coefficient for it.
-/

/--
The coefficient update `nextS ≡ oldS - product (mod m)`: multiplying through by `a`, whatever
`product * a` contributed to `oldS * a` is removed again.
-/
private theorem nextS_mul_mod {m oldS product a X : Nat} (hp : product < m)
    (h : oldS * a % m = (X + product * a) % m) :
    (if product ≤ oldS then oldS - product else m - (product - oldS)) * a % m = X % m := by
  have : (if product ≤ oldS then oldS - product else m - (product - oldS)) % m
      = (oldS + (m - product)) % m := by
    split
    · rw [show oldS + (m - product) = oldS - product + m by omega, Nat.add_mod_right]
    · rw [show m - (product - oldS) = oldS + (m - product) by omega]
  rw [← Nat.mod_mul_mod, this, Nat.mod_mul_mod, Nat.add_mul, Nat.add_mod, h, ← Nat.add_mod,
    Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' (Nat.le_of_lt hp), Nat.add_mul_mod_self_left]

private theorem invMod?_go_spec (modulus : UInt64) (hm : modulus ≠ 0) (a : Nat) :
    ∀ oldR r oldS s : Nat,
      oldS < modulus.toNat → s < modulus.toNat →
      oldS * a % modulus.toNat = oldR % modulus.toNat →
      s * a % modulus.toNat = r % modulus.toNat →
      (invMod?.go modulus oldR r oldS s).1 = Nat.gcd oldR r
        ∧ (invMod?.go modulus oldR r oldS s).2 < modulus.toNat
        ∧ (invMod?.go modulus oldR r oldS s).2 * a % modulus.toNat
            = Nat.gcd oldR r % modulus.toNat := by
  have hm0 : 0 < modulus.toNat := Nat.pos_of_ne_zero (toNat_ne_zero hm)
  intro oldR r oldS s
  induction oldR, r, oldS, s using invMod?.go.induct (modulus := modulus) with
  | case1 oldR oldS s =>
    intro holdS _ h1 _
    rw [invMod?.go, dite_eq_left rfl, Nat.gcd_zero_right]
    exact ⟨rfl, holdS, h1⟩
  | case2 oldR r oldS s hr quotient product nextS ih =>
    intro holdS hs h1 h2
    simp only [quotient, product, nextS] at ih ⊢
    have hnext : nextS < modulus.toNat := by simp only [nextS]; split <;> omega
    have hkey : nextS * a % modulus.toNat = oldR % r % modulus.toNat := by
      refine nextS_mul_mod (Nat.mod_lt _ hm0) ?_
      rw [h1, ← Nat.add_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod, h2,
        Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_div']
    rw [invMod?.go, dite_eq_right hr, Nat.gcd_comm oldR, Nat.gcd_rec r, Nat.gcd_comm]
    exact ih hs hnext h2 hkey

@[simp] theorem invMod?_zero (a : UInt64) : invMod? a 0 = none := by
  simp [invMod?]

private theorem invMod?_spec {a modulus : UInt64} (hm : modulus ≠ 0) :
    (invMod?.go modulus (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0).1
        = Nat.gcd a.toNat modulus.toNat
      ∧ (invMod?.go modulus (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0).2
        < modulus.toNat
      ∧ (invMod?.go modulus (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0).2
          * a.toNat % modulus.toNat
        = Nat.gcd a.toNat modulus.toNat % modulus.toNat := by
  have hm0 : 0 < modulus.toNat := Nat.pos_of_ne_zero (toNat_ne_zero hm)
  have := invMod?_go_spec modulus hm a.toNat (a.toNat % modulus.toNat) modulus.toNat
    (1 % modulus.toNat) 0 (Nat.mod_lt _ hm0) hm0 (by simp) (by simp)
  rwa [← Nat.gcd_rec, Nat.gcd_comm] at this

theorem isSome_invMod? {a modulus : UInt64} (hm : modulus ≠ 0) :
    (invMod? a modulus).isSome ↔ Nat.gcd a.toNat modulus.toNat = 1 := by
  obtain ⟨hg, -, -⟩ := invMod?_spec (a := a) hm
  rw [invMod?]
  simp only [hm, ↓reduceIte]
  split <;> rename_i h <;> simp_all

/-- What `invMod? a modulus = some x` says about `x.toNat`, for a nonzero modulus. -/
private theorem invMod?_eq_some_spec {a modulus x : UInt64} (hm : modulus ≠ 0)
    (h : invMod? a modulus = some x) :
    x.toNat < modulus.toNat ∧ a.toNat * x.toNat % modulus.toNat = 1 % modulus.toNat := by
  obtain ⟨hg, hlt, hinv⟩ := invMod?_spec (a := a) hm
  rw [invMod?] at h
  simp only [hm, ↓reduceIte] at h
  split at h <;> rename_i hgcd <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hlt modulus.toNat_lt)]
  exact ⟨hlt, by rw [Nat.mul_comm, hinv, ← hg, hgcd]⟩

theorem lt_of_invMod?_eq_some {a modulus x : UInt64} (h : invMod? a modulus = some x) :
    x < modulus := by
  by_cases hm : modulus = 0
  · simp [hm] at h
  · exact (invMod?_eq_some_spec hm h).1

/--
The value returned by `invMod?` really is a multiplicative inverse. Note that for `modulus = 1` the
right-hand side is `0`, matching the convention that everything is invertible modulo one.
-/
theorem mulMod_of_invMod?_eq_some {a modulus x : UInt64} (h : invMod? a modulus = some x) :
    mulMod a x modulus = 1 % modulus := by
  by_cases hm : modulus = 0
  · simp [hm] at h
  · rw [← UInt64.toNat_inj, toNat_mulMod hm, UInt64.toNat_mod, UInt64.toNat_one,
      (invMod?_eq_some_spec hm h).2]

private theorem gcd_eq_one_of_mul_mod {A x m : Nat} (h : A * x % m = 1 % m) :
    Nat.gcd A m = 1 := by
  have hd : Nat.gcd A m ∣ 1 % m := h ▸ (Nat.dvd_mod_iff (Nat.gcd_dvd_right A m)).mpr
    (Nat.dvd_trans (Nat.gcd_dvd_left A m) (Nat.dvd_mul_right A x))
  by_cases hm : m = 1
  · simp [hm]
  · rwa [Nat.one_mod_eq_one.mpr hm, Nat.dvd_one] at hd

/-- Two inverses of the same value that are both reduced modulo `m` are equal. -/
private theorem inv_unique {A x y m : Nat} (hx : x < m) (hy : y < m)
    (hax : A * x % m = 1 % m) (hay : A * y % m = 1 % m) : x = y := by
  have key : ∀ {x y}, x < m → A * y % m = 1 % m → x * (A * y) % m = x := fun hx hay => by
    rw [← Nat.mul_mod_mod, hay, Nat.mul_mod_mod, Nat.mul_one, Nat.mod_eq_of_lt hx]
  calc x = x * (A * y) % m := (key hx hay).symm
    _ = y * (A * x) % m := by rw [Nat.mul_left_comm, Nat.mul_left_comm y, Nat.mul_comm x]
    _ = y := key hy hax

/--
`invMod?` returns exactly the reduced multiplicative inverse. The bound `x < modulus` is needed:
without it the equation alone would also admit representatives shifted by `modulus`.
-/
theorem invMod?_eq_some_iff {a modulus x : UInt64} :
    invMod? a modulus = some x ↔ x < modulus ∧ mulMod a x modulus = 1 % modulus := by
  refine ⟨fun h => ⟨lt_of_invMod?_eq_some h, mulMod_of_invMod?_eq_some h⟩, fun ⟨hx, heq⟩ => ?_⟩
  have hm : modulus ≠ 0 := by
    rintro rfl
    simp at hx
  have heq' : a.toNat * x.toNat % modulus.toNat = 1 % modulus.toNat := by
    rw [← toNat_mulMod hm, heq, UInt64.toNat_mod, UInt64.toNat_one]
  have hsome := (isSome_invMod? hm).mpr (gcd_eq_one_of_mul_mod heq')
  obtain ⟨y, hy⟩ : ∃ y, invMod? a modulus = some y := by
    cases hi : invMod? a modulus <;> simp_all
  obtain ⟨hylt, hyinv⟩ := invMod?_eq_some_spec hm hy
  rwa [UInt64.toNat_inj.mp (inv_unique hylt hx hyinv heq')] at hy


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

private theorem toNat_div_two (e : UInt64) : (e / 2).toNat = e.toNat / 2 := by simp

/-- One squaring step: the low bit of `e` goes into the accumulator, then the base is squared. -/
private theorem mul_pow_step (r b e W : Nat) :
    r * b ^ (e % 2) % W * (b * b % W) ^ (e / 2) % W = r * b ^ e % W := by
  rw [Nat.mod_mul_mod, Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod, ← Nat.pow_two, ← Nat.pow_mul,
    Nat.mul_assoc, ← Nat.pow_add, Nat.mod_add_div]

private theorem mul_pow_pow_mod {a b c w k n : Nat} (h : c % n = b ^ w % n) :
    a * c ^ k % n = a * b ^ (w * k) % n := by
  rw [Nat.mul_mod, Nat.pow_mod, h, ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.mul_mod]

private theorem toNat_condMul {base result modulus e : UInt64}
    (hres : result.toNat < wrapMod modulus) :
    (if e % 2 = 1 then mulMod result base modulus else result).toNat
      = result.toNat * base.toNat ^ (e.toNat % 2) % wrapMod modulus := by
  rcases Nat.mod_two_eq_zero_or_one e.toNat with h | h <;>
    simp [← UInt64.toNat_inj, h, toNat_mulMod', Nat.mod_eq_of_lt hres]

private theorem toNat_condMul_lt {base result modulus e : UInt64}
    (hres : result.toNat < wrapMod modulus) :
    (if e % 2 = 1 then mulMod result base modulus else result).toNat < wrapMod modulus := by
  rw [toNat_condMul hres]
  exact Nat.mod_lt _ (wrapMod_pos modulus)

private theorem toNat_powModWord (base e modulus result : UInt64)
    (hres : result.toNat < wrapMod modulus) :
    (powModWord base e modulus result).toNat
      = result.toNat * base.toNat ^ e.toNat % wrapMod modulus := by
  induction base, e, result using powModWord.induct (modulus := modulus) with
  | case1 base result =>
    rw [powModWord, dite_eq_left rfl]
    simp [Nat.mod_eq_of_lt hres]
  | case2 base e result he e' he' =>
    simp only [e'] at he'
    have hlt : e.toNat < 2 := by simpa [← UInt64.toNat_inj, Nat.div_eq_zero_iff] using he'
    rw [powModWord, dite_eq_right he, ite_eq_left he', toNat_condMul hres, Nat.mod_eq_of_lt hlt]
  | case3 base e result he result' e' he' ih =>
    simp only [result', e', dite_eq_ite] at he' ih
    rw [powModWord, dite_eq_right he, ite_eq_right he', ih (toNat_condMul_lt hres),
      toNat_condMul hres, toNat_mulMod', toNat_div_two, mul_pow_step]

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
    rw [powModChunk, show e.toNat = 0 by omega, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hres]
  | succ n ih =>
    have hdiv : (e / 2).toNat < 2 ^ n := by
      rw [toNat_div_two]; rw [Nat.pow_succ] at he; omega
    rw [powModChunk, ih _ _ _ hdiv (toNat_condMul_lt hres), toNat_condMul hres, toNat_mulMod',
      toNat_div_two, mul_pow_step]

private theorem toNat_powModImpl_go (modulus base : UInt64) (e : Nat) (result : UInt64)
    (hres : result.toNat < wrapMod modulus) :
    (powModImpl.go modulus base e result).toNat
      = result.toNat * base.toNat ^ e % wrapMod modulus := by
  induction base, e, result using powModImpl.go.induct (modulus := modulus) with
  | case1 base e result he =>
    rw [powModImpl.go, ite_eq_left he, toNat_powModWord _ _ _ _ hres, Nat.toUInt64,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt he]
  | case2 base e result he b' r' hchunk ih =>
    have hs := toNat_powModChunk_snd modulus 64 base e.toUInt64 result (UInt64.toNat_lt _) hres
    have hf := toNat_powModChunk_fst modulus 64 base e.toUInt64 result
    simp only [hchunk, Nat.toUInt64, UInt64.toNat_ofNat'] at hs hf
    rw [powModImpl.go, ite_eq_right he, hchunk, ih (hs ▸ Nat.mod_lt _ (wrapMod_pos modulus)), hs,
      Nat.mod_mul_mod, mul_pow_pow_mod hf, Nat.mul_assoc, ← Nat.pow_add, Nat.mod_add_div]

@[csimp] theorem powMod_eq_powModImpl : @powMod = @powModImpl := by
  funext base e modulus
  rw [← UInt64.toNat_inj, toNat_powMod', powModImpl]
  by_cases hm : modulus = 1
  · subst hm
    simp [wrapMod, Nat.mod_one]
  · have hM : 1 < wrapMod modulus := by
      have h1 : modulus.toNat ≠ 1 := by simpa [← UInt64.toNat_inj] using hm
      unfold wrapMod; split
      · omega
      · have := toNat_ne_zero ‹_›; omega
    rw [ite_eq_right hm, toNat_powModImpl_go _ _ _ _ (by simpa using hM), UInt64.toNat_one,
      Nat.one_mul]

private theorem toNat_condSub {a b modulus : UInt64} (hb : b < modulus) :
    (if b ≤ a then a - b else modulus - (b - a)).toNat
      = if b.toNat ≤ a.toNat then a.toNat - b.toNat
        else modulus.toNat - (b.toNat - a.toNat) := by
  have hbm : b.toNat < modulus.toNat := hb
  split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le] at h
  · rw [ite_eq_left h, UInt64.toNat_sub_of_le _ _ h]
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_le h)
    have hsub : b - a ≤ modulus := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hab]; omega
    rw [ite_eq_right h, UInt64.toNat_sub_of_le _ _ hsub, UInt64.toNat_sub_of_le _ _ hab]

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
    have hr' : r.toNat ≠ 0 := by simpa [← UInt64.toNat_inj] using hr
    rw [invMod?.go, invModImpl.go]
    simp only [hr, hr', ↓reduceDIte, dite_eq_ite, product, nextS] at ih ⊢
    rw [ih, UInt64.toNat_mod, toNat_condSub (mulMod_lt hm), toNat_mulMod hm, UInt64.toNat_div]

@[csimp] theorem invMod?_eq_invModImpl : @invMod? = @invModImpl := by
  funext a modulus
  by_cases hm : modulus = 0
  · simp [invMod?, invModImpl, hm]
  · simp [invMod?, invModImpl, hm, invModImpl_go_eq modulus hm]

end UInt64
