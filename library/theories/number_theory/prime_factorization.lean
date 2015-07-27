/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Multiplicity and prime factors. We have:

  mult p n        := the greatest power of p dividing n if p > 1 and n > 0, and 0 otherwise.
  prime_factors n := the finite set of prime factors of n, assuming n > 0

-/
import data.nat data.finset .primes
open eq.ops finset well_founded decidable

namespace nat

-- TODO: this should be proved more generally in ring_bigops
theorem Prod_pos {A : Type} [deceqA : decidable_eq A]
    {s : finset A} {f : A → ℕ} (fpos : ∀ n, n ∈ s → f n > 0) :
  (∏ n ∈ s, f n) > 0 :=
begin
  induction s with a s anins ih,
    {rewrite Prod_empty; exact zero_lt_one},
  rewrite [!Prod_insert_of_not_mem anins],
  exact (mul_pos (fpos a (mem_insert a _)) (ih (forall_of_forall_insert fpos)))
end

/- multiplicity -/

theorem mult_rec_decreasing {p n : ℕ} (Hp : p > 1) (Hn : n > 0) : n div p < n :=
have H' : n < n * p,
 by rewrite [-mul_one n at {1}]; apply mul_lt_mul_of_pos_left Hp Hn,
div_lt_of_lt_mul H'

private definition mult.F (p : ℕ) (n : ℕ) (f: Π {m : ℕ}, m < n → ℕ) : ℕ :=
if H : (p > 1 ∧ n > 0) ∧ p ∣ n then
  succ (f (mult_rec_decreasing (and.left (and.left H)) (and.right (and.left H))))
else 0

definition mult (p n : ℕ) : ℕ := fix (mult.F p) n

theorem mult_rec {p n : ℕ} (pgt1 : p > 1) (ngt0 : n > 0) (pdivn : p ∣ n) :
  mult p n = succ (mult p (n div p)) :=
have (p > 1 ∧ n > 0) ∧ p ∣ n, from and.intro (and.intro pgt1 ngt0) pdivn,
eq.trans (well_founded.fix_eq (mult.F p) n) (dif_pos this)

private theorem mult_base {p n : ℕ} (H : ¬ ((p > 1 ∧ n > 0) ∧ p ∣ n)) :
  mult p n = 0 :=
eq.trans (well_founded.fix_eq (mult.F p) n) (dif_neg H)

theorem mult_zero_right (p : ℕ) : mult p 0 = 0 :=
mult_base (assume H, !lt.irrefl (and.right (and.left H)))

theorem mult_eq_zero_of_not_dvd {p n : ℕ} (H : ¬ p ∣ n) : mult p n = 0 :=
mult_base (assume H', H (and.right H'))

theorem mult_eq_zero_of_le_one {p : ℕ} (n : ℕ) (H : p ≤ 1) : mult p n = 0 :=
mult_base (assume H', not_lt_of_ge H (and.left (and.left H')))

theorem mult_zero_left (n : ℕ) : mult 0 n = 0 :=
mult_eq_zero_of_le_one n !dec_trivial

theorem mult_one_left (n : ℕ) : mult 1 n = 0 :=
mult_eq_zero_of_le_one n !dec_trivial

theorem mult_pos_of_dvd {p n : ℕ} (pgt1 : p > 1) (npos : n > 0) (pdvdn : p ∣ n) : mult p n > 0 :=
by rewrite (mult_rec pgt1 npos pdvdn); apply succ_pos

theorem not_dvd_of_mult_eq_zero {p n : ℕ} (pgt1 : p > 1) (npos : n > 0) (H : mult p n = 0) :
  ¬ p ∣ n :=
suppose p ∣ n,
ne_of_gt (mult_pos_of_dvd pgt1 npos this) H

theorem dvd_of_mult_pos {p n : ℕ} (H : mult p n > 0) : p ∣ n :=
by_contradiction (suppose ¬ p ∣ n, ne_of_gt H (mult_eq_zero_of_not_dvd this))

/- properties of mult -/

theorem mult_eq_zero_of_prime_of_ne {p q : ℕ} (primep : prime p) (primeq : prime q)
    (pneq : p ≠ q) :
  mult p q = 0 :=
mult_eq_zero_of_not_dvd (not_dvd_of_prime_of_coprime primep (coprime_primes primep primeq pneq))

theorem pow_mult_dvd (p n : ℕ) : p^(mult p n) ∣ n :=
begin
  induction n using nat.strong_induction_on with [n, ih],
  cases eq_zero_or_pos n with [nz, npos],
    {rewrite nz, apply dvd_zero},
  cases le_or_gt p 1 with [ple1, pgt1],
    {rewrite [!mult_eq_zero_of_le_one ple1, pow_zero], apply one_dvd},
  cases (or.swap (em (p ∣ n))) with [pndvdn, pdvdn],
    {rewrite [mult_eq_zero_of_not_dvd pndvdn, pow_zero], apply one_dvd},
  show p ^ (mult p n) ∣ n, from dvd.elim pdvdn
    (take n',
      suppose n = p * n',
      have p > 0, from lt.trans zero_lt_one pgt1,
      assert n div p = n', from !div_eq_of_eq_mul_right this `n = p * n'`,
      assert n' < n,
        by rewrite -this; apply mult_rec_decreasing pgt1 npos,
      begin
        rewrite [mult_rec pgt1 npos pdvdn, `n div p = n'`, pow_succ'], subst n,
        apply mul_dvd_mul !dvd.refl,
        apply ih _ this
      end)
end

theorem mult_one_right (p : ℕ) : mult p 1 = 0:=
assert H : p^(mult p 1) = 1, from eq_one_of_dvd_one !pow_mult_dvd,
or.elim (le_or_gt p 1)
  (suppose p ≤ 1, by rewrite [!mult_eq_zero_of_le_one this])
  (suppose p > 1,
    by_contradiction
      (suppose mult p 1 ≠ 0,
       have mult p 1 > 0,       from pos_of_ne_zero this,
       assert p^(mult p 1) > 1, from pow_gt_one `p > 1` this,
       show false,              by rewrite H at this; apply !lt.irrefl this))

private theorem mult_pow_mul {p n : ℕ} (i : ℕ) (pgt1 : p > 1) (npos : n > 0) :
  mult p (p^i * n) = i + mult p n :=
begin
  induction i with [i, ih],
    {rewrite [pow_zero, one_mul, zero_add]},
  have p > 0, from lt.trans zero_lt_one pgt1,
  have psin_pos : p^(succ i) * n > 0, from mul_pos (!pow_pos_of_pos this) npos,
  have p ∣ p^(succ i) * n, by rewrite [pow_succ', mul.assoc]; apply dvd_mul_right,
  rewrite [mult_rec pgt1 psin_pos this, pow_succ, mul.right_comm, !mul_div_cancel `p > 0`, ih],
  rewrite [add.comm i, add.comm (succ i)]
end

theorem mult_pow_self {p : ℕ} (i : ℕ) (pgt1 : p > 1) : mult p (p^i) = i :=
by rewrite [-(mul_one (p^i)), mult_pow_mul i pgt1 zero_lt_one, mult_one_right]

theorem le_mult {p i n : ℕ} (pgt1 : p > 1) (npos : n > 0) (pidvd : p^i ∣ n) : i ≤ mult p n :=
dvd.elim pidvd
  (take m,
    suppose n = p^i * m,
    assert m > 0, from pos_of_mul_pos_left (this ▸ npos),
    by subst n; rewrite [mult_pow_mul i pgt1 this]; apply le_add_right)

theorem not_dvd_div_pow_mult {p n : ℕ} (pgt1 : p > 1) (npos : n > 0) : ¬ p ∣ n div p^(mult p n) :=
assume pdvd : p ∣ n div p^(mult p n),
obtain m (H : n div p^(mult p n) = p * m), from exists_eq_mul_right_of_dvd pdvd,
assert n = p^(succ (mult p n)) * m, from
  calc
    n     = p^mult p n * (n div p^mult p n) : by rewrite (mul_div_cancel' !pow_mult_dvd)
      ... = p^(succ (mult p n)) * m         : by rewrite [H, pow_succ, mul.assoc],
have p^(succ (mult p n)) ∣ n,    by rewrite this at {2}; apply dvd_mul_right,
have succ (mult p n) ≤ mult p n, from le_mult pgt1 npos this,
show false,                      from !not_succ_le_self this

theorem mult_mul {p m n : ℕ} (primep : prime p) (mpos : m > 0) (npos : n > 0) :
  mult p (m * n) = mult p m + mult p n :=
let m' := m div p^mult p m, n' := n div p^mult p n in
assert p > 1, from gt_one_of_prime primep,
assert meq : m = p^mult p m * m', by rewrite (mul_div_cancel' !pow_mult_dvd),
assert neq : n = p^mult p n * n', by rewrite (mul_div_cancel' !pow_mult_dvd),
have m'pos : m' > 0, from pos_of_mul_pos_left (meq ▸ mpos),
have n'pos : n' > 0, from pos_of_mul_pos_left (neq ▸ npos),
have npdvdm' : ¬ p ∣ m', from !not_dvd_div_pow_mult `p > 1` mpos,
have npdvdn' : ¬ p ∣ n', from !not_dvd_div_pow_mult `p > 1` npos,
assert npdvdm'n' : ¬ p ∣ m' * n', from not_dvd_mul_of_prime primep npdvdm' npdvdn',
assert m'n'pos : m' * n' > 0, from mul_pos m'pos n'pos,
assert multm'n' : mult p (m' * n') = 0, from mult_eq_zero_of_not_dvd npdvdm'n',
calc
  mult p (m * n) = mult p (p^(mult p m + mult p n) * (m' * n')) :
                     by rewrite [pow_add, mul.right_comm, -mul.assoc, -meq, mul.assoc,
                                 mul.comm (n div _), -neq]
             ... = mult p m + mult p n                          :
                     by rewrite [!mult_pow_mul `p > 1` m'n'pos, multm'n']

theorem dvd_of_forall_prime_mult_le {m n : ℕ} (mpos : m > 0)
    (H : ∀ {p}, prime p → mult p m ≤ mult p n) :
  m ∣ n :=
begin
  revert H, revert n,
  induction m using nat.strong_induction_on with [m, ih],
  cases (decidable.em (m = 1)) with [meq, mneq],
    {intros, rewrite meq, apply one_dvd},
  have mgt1 : m > 1, from lt_of_le_of_ne (succ_le_of_lt mpos) (ne.symm mneq),
  have mge2 : m ≥ 2, from succ_le_of_lt mgt1,
  have hpd : ∃ p, prime p ∧ p ∣ m, from ex_prime_and_dvd mge2,
  cases hpd with [p, H1],
  cases H1 with [primep, pdvdm],
  intro n,
  cases (eq_zero_or_pos n) with [nz, npos],
    {intros; rewrite nz; apply dvd_zero},
  assume H : ∀ {p : ℕ}, prime p → mult p m ≤ mult p n,
  obtain m' (meq : m = p * m'), from exists_eq_mul_right_of_dvd pdvdm,
  assert pgt1 : p > 1, from gt_one_of_prime primep,
  assert m'pos : m' > 0, from pos_of_ne_zero
      (assume m'z, by revert mpos; rewrite [meq, m'z, mul_zero]; apply not_lt_zero),
  have m'ltm : m' < m,
    by rewrite [meq, -one_mul m' at {1}]; apply mul_lt_mul_of_lt_of_le m'pos pgt1 !le.refl,
  have multpm : mult p m ≥ 1, from le_mult pgt1 mpos (by rewrite pow_one; apply pdvdm),
  have multpn : mult p n ≥ 1, from le.trans multpm (H primep),
  obtain n' (neq : n = p * n'),
    from exists_eq_mul_right_of_dvd (dvd_of_mult_pos (lt_of_succ_le multpn)),
  assert n'pos : n' > 0, from pos_of_ne_zero
      (assume n'z, by revert npos; rewrite [neq, n'z, mul_zero]; apply not_lt_zero),
  have ∀q, prime q → mult q m' ≤ mult q n', from
    (take q,
      assume primeq : prime q,
      have multqm : mult q m = mult q p + mult q m',
        by rewrite [meq, mult_mul primeq (pos_of_prime primep) m'pos],
      have multqn : mult q n = mult q p + mult q n',
        by rewrite [neq, mult_mul primeq (pos_of_prime primep) n'pos],
      show mult q m' ≤ mult q n', from le_of_add_le_add_left (multqm ▸ multqn ▸ H primeq)),
  assert m'dvdn' : m' ∣ n', from ih m' m'ltm m'pos n' this,
  show m ∣ n, by rewrite [meq, neq]; apply mul_dvd_mul !dvd.refl m'dvdn'
end

theorem eq_of_forall_prime_mult_eq {m n : ℕ} (mpos : m > 0) (npos : n > 0)
    (H : ∀ p, prime p → mult p m = mult p n) : m = n :=
dvd.antisymm
  (dvd_of_forall_prime_mult_le mpos (take p, assume primep, H _ primep ▸ !le.refl))
  (dvd_of_forall_prime_mult_le npos (take p, assume primep, H _ primep ▸ !le.refl))

/- prime factors -/

definition prime_factors (n : ℕ) : finset ℕ := { p ∈ upto (succ n) | prime p ∧ p ∣ n }

theorem prime_of_mem_prime_factors {p n : ℕ} (H : p ∈ prime_factors n) : prime p :=
and.left (of_mem_filter H)

theorem dvd_of_mem_prime_factors {p n : ℕ} (H : p ∈ prime_factors n) : p ∣ n :=
and.right (of_mem_filter H)

theorem mem_prime_factors {p n : ℕ} (npos : n > 0) (primep : prime p) (pdvdn : p ∣ n) :
  p ∈ prime_factors n :=
have plen : p ≤ n, from le_of_dvd npos pdvdn,
mem_filter_of_mem (mem_upto_of_lt (lt_succ_of_le plen)) (and.intro primep pdvdn)

/- prime factorization -/

theorem mult_pow_eq_zero_of_prime_of_ne {p q : ℕ} (primep : prime p) (primeq : prime q)
  (pneq : p ≠ q) (i : ℕ) : mult p (q^i) = 0 :=
begin
  induction i with i ih,
    {rewrite [pow_zero, mult_one_right]},
  have qpos : q > 0, from pos_of_prime primeq,
  have qipos : q^i > 0, from !pow_pos_of_pos qpos,
  rewrite [pow_succ, mult_mul primep qipos qpos, ih, mult_eq_zero_of_prime_of_ne primep primeq pneq]
end

theorem mult_prod_pow_of_not_mem {p : ℕ} (primep : prime p) {s : finset ℕ}
    (sprimes : ∀ p, p ∈ s → prime p) (f : ℕ → ℕ) (pns : p ∉ s) :
  mult p (∏ q ∈ s, q^(f q)) = 0 :=
begin
  induction s with a s anins ih,
    {rewrite [Prod_empty, mult_one_right]},
  have pnea : p ≠ a, from assume peqa, by rewrite peqa at pns; exact pns !mem_insert,
  have primea : prime a, from sprimes a !mem_insert,
  have afapos : a ^ f a > 0, from !pow_pos_of_pos (pos_of_prime primea),
  have prodpos : (∏ q ∈ s, q ^ f q) > 0,
    from Prod_pos (take q, assume qs,
      !pow_pos_of_pos (pos_of_prime (forall_of_forall_insert sprimes q qs))),
  rewrite [!Prod_insert_of_not_mem anins, mult_mul primep afapos prodpos],
  rewrite (mult_pow_eq_zero_of_prime_of_ne primep primea pnea),
  rewrite (ih (forall_of_forall_insert sprimes) (λ H, pns (!mem_insert_of_mem H)))
end

theorem mult_prod_pow_of_mem {p : ℕ} (primep : prime p) {s : finset ℕ}
    (sprimes : ∀ p, p ∈ s → prime p) (f : ℕ → ℕ) (ps : p ∈ s) :
  mult p (∏ q ∈ s, q^(f q)) = f p :=
begin
  induction s with a s anins ih,
    {exact absurd ps !not_mem_empty},
  have primea : prime a, from sprimes a !mem_insert,
  have afapos : a ^ f a > 0, from !pow_pos_of_pos (pos_of_prime primea),
  have prodpos : (∏ q ∈ s, q ^ f q) > 0,
    from Prod_pos (take q, assume qs,
      !pow_pos_of_pos (pos_of_prime (forall_of_forall_insert sprimes q qs))),
  rewrite [!Prod_insert_of_not_mem anins, mult_mul primep afapos prodpos],
  cases eq_or_mem_of_mem_insert ps with peqa pins,
    {rewrite [peqa, !mult_pow_self (gt_one_of_prime primea)],
      rewrite [mult_prod_pow_of_not_mem primea (forall_of_forall_insert sprimes) _ anins]},
  have pnea : p ≠ a, from by intro peqa; rewrite peqa at pins; exact anins pins,
  rewrite [mult_pow_eq_zero_of_prime_of_ne primep primea pnea, zero_add],
  exact (ih (forall_of_forall_insert sprimes) pins)
end

theorem eq_prime_factorization {n : ℕ} (npos : n > 0) :
  n = (∏ p ∈ prime_factors n, p^(mult p n)) :=
let nprod := ∏ p ∈ prime_factors n, p^(mult p n) in
assert primefactors : ∀ p, p ∈ prime_factors n → prime p,
  from take p, @prime_of_mem_prime_factors p n,
have prodpos : (∏ q ∈ prime_factors n, q^(mult q n)) > 0,
  from Prod_pos (take q, assume qpf,
    !pow_pos_of_pos (pos_of_prime (prime_of_mem_prime_factors qpf))),
eq_of_forall_prime_mult_eq npos prodpos
  (take p,
    assume primep,
    decidable.by_cases
      (assume pprimefactors : p ∈ prime_factors n,
        eq.symm (mult_prod_pow_of_mem primep primefactors (λ p, mult p n) pprimefactors))
      (assume pnprimefactors : p ∉ prime_factors n,
        have ¬ p ∣ n, from assume H, pnprimefactors (mem_prime_factors npos primep H),
        assert mult p n = 0, from mult_eq_zero_of_not_dvd this,
        by rewrite [this, mult_prod_pow_of_not_mem primep primefactors _ pnprimefactors]))
end nat
