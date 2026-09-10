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

@[simp] theorem toNat_mulMod_zero {a b : UInt64} :
    (mulMod a b 0).toNat = a.toNat * b.toNat % 2 ^ 64 := by
  rw [toNat_mulMod']
  rfl

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

@[simp] theorem toNat_powMod_zero {base : UInt64} {e : Nat} :
    (powMod base e 0).toNat = base.toNat ^ e % 2 ^ 64 := by
  rw [toNat_powMod']
  rfl

theorem powMod_lt {base : UInt64} {e : Nat} {modulus : UInt64} (h : modulus ≠ 0) :
    powMod base e modulus < modulus := by
  rw [UInt64.lt_iff_toNat_lt, toNat_powMod h]
  exact Nat.mod_lt _ (Nat.zero_lt_of_ne_zero (toNat_ne_zero h))

/-! ### Correctness of `invMod?`

`invMod?.go` is the extended Euclidean algorithm carrying a single coefficient sequence. Writing
`a` for the value being inverted, it maintains `oldS * a ≡ oldR` and `s * a ≡ r` modulo `modulus`,
while `Nat.gcd oldR r` stays fixed. At exit `r = 0`, so the first component is the gcd and the
second is a Bézout coefficient for it.
-/

private theorem add_right_cancel_mod {x y k m : Nat} (hm : 0 < m)
    (h : (x + k) % m = (y + k) % m) : x % m = y % m := by
  have h1 := Nat.div_add_mod k m
  have h2 : k % m < m := Nat.mod_lt _ hm
  have h3 : m * (k / m + 1) = m * (k / m) + m := Nat.mul_succ m (k / m)
  have hk : k + (m - k % m) = m * (k / m + 1) := by omega
  have key : ∀ z : Nat, (z + (k + (m - k % m))) % m = z % m := by
    intro z; rw [hk, Nat.add_mul_mod_self_left]
  rw [← key x, ← key y, ← Nat.add_assoc, ← Nat.add_assoc, Nat.add_mod (x + k), h,
    ← Nat.add_mod]

private theorem add_nextS_mod (m oldS product : Nat) (hp : product < m) :
    ((if product ≤ oldS then oldS - product else m - (product - oldS)) + product) % m
      = oldS % m := by
  by_cases h : product ≤ oldS
  · simp only [h, ↓reduceIte]
    congr 1
    omega
  · simp only [h, ↓reduceIte]
    rw [show m - (product - oldS) + product = m + oldS by omega, Nat.add_mod_left]

private theorem invMod?_go_spec (modulus : UInt64) (hm : modulus ≠ 0) (a : Nat) :
    ∀ oldR r oldS s : Nat,
      oldS < modulus.toNat → s < modulus.toNat →
      oldS * a % modulus.toNat = oldR % modulus.toNat →
      s * a % modulus.toNat = r % modulus.toNat →
      (invMod?.go modulus oldR r oldS s).1 = Nat.gcd oldR r
        ∧ (invMod?.go modulus oldR r oldS s).2 < modulus.toNat
        ∧ (invMod?.go modulus oldR r oldS s).2 * a % modulus.toNat
            = Nat.gcd oldR r % modulus.toNat := by
  have hm0 : 0 < modulus.toNat := Nat.zero_lt_of_ne_zero (toNat_ne_zero hm)
  intro oldR r oldS s
  induction oldR, r, oldS, s using invMod?.go.induct (modulus := modulus) with
  | case1 oldR oldS s =>
    intro holdS _ h1 _
    rw [invMod?.go]
    simp only [↓reduceDIte, Nat.gcd_zero_right]
    refine ⟨?_, ?_, ?_⟩
    · trivial
    · exact holdS
    · exact h1
  | case2 oldR r oldS s hr quotient product nextS ih =>
    intro holdS hs h1 h2
    simp only [quotient, product, nextS] at ih ⊢
    have hplt : quotient * s % modulus.toNat < modulus.toNat := Nat.mod_lt _ hm0
    have hnext : nextS < modulus.toNat := by
      simp only [nextS]
      split <;> omega
    have hprod : (quotient * s % modulus.toNat) * a % modulus.toNat
        = quotient * r % modulus.toNat := by
      rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod, h2, Nat.mul_mod_mod]
    have hkey : nextS * a % modulus.toNat = (oldR % r) % modulus.toNat := by
      refine add_right_cancel_mod (k := quotient * r) hm0 ?_
      rw [show oldR % r + quotient * r = oldR by
        have h := Nat.div_add_mod oldR r
        simp only [quotient]
        rw [Nat.mul_comm (oldR / r) r]
        omega]
      rw [Nat.add_mod, ← hprod, ← Nat.add_mod, ← Nat.add_mul, ← Nat.mod_mul_mod]
      simp only [nextS, dite_eq_ite]
      rw [add_nextS_mod _ _ _ hplt, Nat.mod_mul_mod, h1]
    rw [invMod?.go]
    simp only [hr, ↓reduceDIte]
    have := ih hs hnext h2 hkey
    rw [show Nat.gcd r (oldR % r) = Nat.gcd oldR r by
      rw [Nat.gcd_comm r (oldR % r), ← Nat.gcd_rec, Nat.gcd_comm]] at this
    exact this

@[simp] theorem invMod?_zero (a : UInt64) : invMod? a 0 = none := by
  rw [invMod?]
  simp

private theorem invMod?_spec {a modulus : UInt64} (hm : modulus ≠ 0) :
    (invMod?.go modulus (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0).1
        = Nat.gcd a.toNat modulus.toNat
      ∧ (invMod?.go modulus (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0).2
        < modulus.toNat
      ∧ (invMod?.go modulus (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0).2
          * a.toNat % modulus.toNat
        = Nat.gcd a.toNat modulus.toNat % modulus.toNat := by
  have hm0 : 0 < modulus.toNat := Nat.zero_lt_of_ne_zero (toNat_ne_zero hm)
  have hgcd : Nat.gcd (a.toNat % modulus.toNat) modulus.toNat
      = Nat.gcd a.toNat modulus.toNat := by
    rw [← Nat.gcd_rec, Nat.gcd_comm]
  have := invMod?_go_spec modulus hm a.toNat (a.toNat % modulus.toNat) modulus.toNat
    (1 % modulus.toNat) 0 (Nat.mod_lt _ hm0) hm0
    (by rw [Nat.mod_mul_mod, Nat.one_mul, Nat.mod_mod])
    (by rw [Nat.zero_mul, Nat.zero_mod, Nat.mod_self])
  rwa [hgcd] at this

theorem isSome_invMod? {a modulus : UInt64} (hm : modulus ≠ 0) :
    (invMod? a modulus).isSome ↔ Nat.gcd a.toNat modulus.toNat = 1 := by
  obtain ⟨hg, -, -⟩ := invMod?_spec (a := a) hm
  rw [invMod?]
  simp only [hm, ↓reduceIte]
  split <;> rename_i h <;> simp_all

theorem lt_of_invMod?_eq_some {a modulus x : UInt64} (h : invMod? a modulus = some x) :
    x < modulus := by
  by_cases hm : modulus = 0
  · simp [hm] at h
  · obtain ⟨-, hlt, -⟩ := invMod?_spec (a := a) hm
    rw [invMod?] at h
    simp only [hm, ↓reduceIte] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    have hmlt := modulus.toNat_lt
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    exact hlt

/--
The value returned by `invMod?` really is a multiplicative inverse. Note that for `modulus = 1` the
right-hand side is `0`, matching the convention that everything is invertible modulo one.
-/
theorem mulMod_of_invMod?_eq_some {a modulus x : UInt64} (h : invMod? a modulus = some x) :
    mulMod a x modulus = 1 % modulus := by
  by_cases hm : modulus = 0
  · simp [hm] at h
  · obtain ⟨hg, hlt, hinv⟩ := invMod?_spec (a := a) hm
    rw [invMod?] at h
    simp only [hm, ↓reduceIte] at h
    split at h <;> rename_i hgcd <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    have hx : (UInt64.ofNat
        (invMod?.go modulus (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0).2).toNat
        = (invMod?.go modulus (a.toNat % modulus.toNat) modulus.toNat
            (1 % modulus.toNat) 0).2 := by
      have hmlt := modulus.toNat_lt
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    rw [← UInt64.toNat_inj, toNat_mulMod hm, hx, UInt64.toNat_mod,
      show (1 : UInt64).toNat = 1 from rfl, Nat.mul_comm, hinv, ← hg, hgcd]

private theorem gcd_eq_one_of_mul_mod {A x m : Nat} (hm : 0 < m) (h : A * x % m = 1 % m) :
    Nat.gcd A m = 1 := by
  have hd : Nat.gcd A m ∣ 1 % m := by
    have hsplit : m * (A * x / m) + A * x % m = A * x := Nat.div_add_mod _ _
    have h1 : Nat.gcd A m ∣ A * x := Nat.dvd_trans (Nat.gcd_dvd_left A m) (Nat.dvd_mul_right A x)
    have h2 : Nat.gcd A m ∣ m * (A * x / m) :=
      Nat.dvd_trans (Nat.gcd_dvd_right A m) (Nat.dvd_mul_right m _)
    have := Nat.dvd_sub h1 h2
    rwa [show A * x - m * (A * x / m) = 1 % m by omega] at this
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have : m = 1 := by omega
    subst this
    simp
  · rw [Nat.mod_eq_of_lt (by omega)] at hd
    exact Nat.dvd_one.mp hd

/-- Two inverses of the same value that are both reduced modulo `m` are equal. -/
private theorem inv_unique {A x y m : Nat} (hx : x < m) (hy : y < m)
    (hax : A * x % m = 1 % m) (hay : A * y % m = 1 % m) : x = y := by
  have key : x % m = y % m := by
    calc x % m
        = x * 1 % m := by rw [Nat.mul_one]
      _ = x * (1 % m) % m := by rw [Nat.mul_mod_mod]
      _ = x * (A * y % m) % m := by rw [hay]
      _ = x * (A * y) % m := by rw [Nat.mul_mod_mod]
      _ = A * x * y % m := by rw [← Nat.mul_assoc, Nat.mul_comm x A]
      _ = A * x % m * y % m := by rw [Nat.mod_mul_mod]
      _ = 1 % m * y % m := by rw [hax]
      _ = 1 * y % m := by rw [Nat.mod_mul_mod]
      _ = y % m := by rw [Nat.one_mul]
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at key

/--
`invMod?` returns exactly the reduced multiplicative inverse. The bound `x < modulus` is needed:
without it the equation alone would also admit representatives shifted by `modulus`.
-/
theorem invMod?_eq_some_iff {a modulus x : UInt64} :
    invMod? a modulus = some x ↔ x < modulus ∧ mulMod a x modulus = 1 % modulus := by
  refine ⟨fun h => ⟨lt_of_invMod?_eq_some h, mulMod_of_invMod?_eq_some h⟩, fun ⟨hx, heq⟩ => ?_⟩
  have hm : modulus ≠ 0 := by
    rintro rfl
    exact absurd hx (by simp)
  have hm0 : 0 < modulus.toNat := Nat.zero_lt_of_ne_zero (toNat_ne_zero hm)
  have hxm : x.toNat < modulus.toNat := UInt64.lt_iff_toNat_lt.mp hx
  have heq' : a.toNat * x.toNat % modulus.toNat = 1 % modulus.toNat := by
    rw [← toNat_mulMod hm, heq, UInt64.toNat_mod, show (1 : UInt64).toNat = 1 from rfl]
  have hsome := (isSome_invMod? hm).mpr (gcd_eq_one_of_mul_mod hm0 heq')
  obtain ⟨y, hy⟩ : ∃ y, invMod? a modulus = some y := by
    cases hi : invMod? a modulus with
    | none => rw [hi] at hsome; simp at hsome
    | some y => exact ⟨y, rfl⟩
  have hyx : y.toNat = x.toNat := by
    refine inv_unique (UInt64.lt_iff_toNat_lt.mp (lt_of_invMod?_eq_some hy)) hxm ?_ heq'
    rw [← toNat_mulMod hm, mulMod_of_invMod?_eq_some hy, UInt64.toNat_mod,
      show (1 : UInt64).toNat = 1 from rfl]
  rwa [UInt64.toNat_inj.mp hyx] at hy


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
