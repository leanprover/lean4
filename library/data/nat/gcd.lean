/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Definitions and properties of gcd, lcm, and coprime.
-/
import .div
open eq.ops well_founded decidable prod

namespace nat

/- gcd -/

private definition pair_nat.lt : nat × nat → nat × nat → Prop := measure pr₂
private definition pair_nat.lt.wf : well_founded pair_nat.lt :=
intro_k (measure.wf pr₂) 20  -- we use intro_k to be able to execute gcd efficiently in the kernel

local attribute pair_nat.lt.wf [instance]      -- instance will not be saved in .olean
local infixl `≺`:50 := pair_nat.lt

private definition gcd.lt.dec (x y₁ : nat) : (succ y₁, x mod succ y₁) ≺ (x, succ y₁) :=
!mod_lt (succ_pos y₁)

definition gcd.F : Π (p₁ : nat × nat), (Π p₂ : nat × nat, p₂ ≺ p₁ → nat) → nat
| (x, 0)      f := x
| (x, succ y) f := f (succ y, x mod succ y) !gcd.lt.dec

definition gcd (x y : nat) := fix gcd.F (x, y)

theorem gcd_zero_right (x : nat) : gcd x 0 = x := rfl

theorem gcd_succ (x y : nat) : gcd x (succ y) = gcd (succ y) (x mod succ y) :=
well_founded.fix_eq gcd.F (x, succ y)

theorem gcd_one_right (n : ℕ) : gcd n 1 = 1 :=
calc gcd n 1 = gcd 1 (n mod 1) : gcd_succ
         ... = gcd 1 0         : mod_one

theorem gcd_def (x : ℕ) : Π (y : ℕ), gcd x y = if y = 0 then x else gcd y (x mod y)
| 0        := !gcd_zero_right
| (succ y) := !gcd_succ ⬝ (if_neg !succ_ne_zero)⁻¹


theorem gcd_self : Π (n : ℕ), gcd n n = n
| 0         := rfl
| (succ n₁) := calc
    gcd (succ n₁) (succ n₁) = gcd (succ n₁) (succ n₁ mod succ n₁) : gcd_succ
                      ...   = gcd (succ n₁) 0                     : mod_self

theorem gcd_zero_left : Π (n : ℕ), gcd 0 n = n
| 0         := rfl
| (succ n₁) := calc
    gcd 0 (succ n₁) = gcd (succ n₁) (0 mod succ n₁) : gcd_succ
                ... = gcd (succ n₁) 0               : zero_mod

theorem gcd_of_pos (m : ℕ) {n : ℕ} (H : n > 0) : gcd m n = gcd n (m mod n) :=
gcd_def m n ⬝ if_neg (ne_zero_of_pos H)

theorem gcd_rec (m n : ℕ) : gcd m n = gcd n (m mod n) :=
by_cases_zero_pos n
  (calc
          m = gcd 0 m         : gcd_zero_left
        ... = gcd 0 (m mod 0) : mod_zero)
  (take n, assume H : 0 < n, gcd_of_pos m H)

theorem gcd.induction {P : ℕ → ℕ → Prop}
                   (m n : ℕ)
                   (H0 : ∀m, P m 0)
                   (H1 : ∀m n, 0 < n → P n (m mod n) → P m n) :
                 P m n :=
induction (m, n) (prod.rec (λm, nat.rec (λ IH, H0 m)
   (λ n₁ v (IH : ∀p₂, p₂ ≺ (m, succ n₁) → P (pr₁ p₂) (pr₂ p₂)),
      H1 m (succ n₁) !succ_pos (IH _ !gcd.lt.dec))))

theorem gcd_dvd (m n : ℕ) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) :=
gcd.induction m n
  (take m, and.intro (!one_mul ▸ !dvd_mul_left) !dvd_zero)
  (take m n (npos : 0 < n), and.rec
     (assume (IH₁ : gcd n (m mod n) ∣ n) (IH₂ : gcd n (m mod n) ∣ (m mod n)),
    have H : (gcd n (m mod n) ∣ (m div n * n + m mod n)), from
      dvd_add (dvd.trans IH₁ !dvd_mul_left) IH₂,
    have H1 : (gcd n (m mod n) ∣ m), from !eq_div_mul_add_mod⁻¹ ▸ H,
    show (gcd m n ∣ m) ∧ (gcd m n ∣ n), from !gcd_rec⁻¹ ▸ (and.intro H1 IH₁)))

theorem gcd_dvd_left (m n : ℕ) : gcd m n ∣ m := and.left !gcd_dvd

theorem gcd_dvd_right (m n : ℕ) : gcd m n ∣ n := and.right !gcd_dvd

theorem dvd_gcd {m n k : ℕ} : k ∣ m → k ∣ n → k ∣ gcd m n :=
gcd.induction m n (take m, imp.intro)
  (take m n (npos : n > 0)
    (IH : k ∣ n → k ∣ m mod n → k ∣ gcd n (m mod n))
    (H1 : k ∣ m) (H2 : k ∣ n),
    have H3 : k ∣ m div n * n + m mod n, from !eq_div_mul_add_mod ▸ H1,
    have H4 : k ∣ m mod n, from dvd_of_dvd_add_left H3 (dvd.trans H2 !dvd_mul_left),
    !gcd_rec⁻¹ ▸ IH H2 H4)

theorem gcd.comm (m n : ℕ) : gcd m n = gcd n m :=
dvd.antisymm
  (dvd_gcd !gcd_dvd_right !gcd_dvd_left)
  (dvd_gcd !gcd_dvd_right !gcd_dvd_left)

theorem gcd.assoc (m n k : ℕ) : gcd (gcd m n) k = gcd m (gcd n k) :=
dvd.antisymm
  (dvd_gcd
    (dvd.trans !gcd_dvd_left !gcd_dvd_left)
    (dvd_gcd (dvd.trans !gcd_dvd_left !gcd_dvd_right) !gcd_dvd_right))
  (dvd_gcd
    (dvd_gcd !gcd_dvd_left (dvd.trans !gcd_dvd_right !gcd_dvd_left))
    (dvd.trans !gcd_dvd_right !gcd_dvd_right))

theorem gcd_one_left (m : ℕ) : gcd 1 m = 1 :=
!gcd.comm ⬝ !gcd_one_right

theorem gcd_mul_left (m n k : ℕ) : gcd (m * n) (m * k) = m * gcd n k :=
gcd.induction n k
  (take n, calc gcd (m * n) (m * 0) = gcd (m * n) 0 : mul_zero)
  (take n k,
    assume H : 0 < k,
    assume IH : gcd (m * k) (m * (n mod k)) = m * gcd k (n mod k),
    calc
      gcd (m * n) (m * k) = gcd (m * k) (m * n mod (m * k)) : !gcd_rec
                      ... = gcd (m * k) (m * (n mod k))     : mul_mod_mul_left
                      ... = m * gcd k (n mod k)             : IH
                      ... = m * gcd n k                     : !gcd_rec)

theorem gcd_mul_right (m n k : ℕ) : gcd (m * n) (k * n) = gcd m k * n :=
calc
  gcd (m * n) (k * n) = gcd (n * m) (k * n) : mul.comm
                  ... = gcd (n * m) (n * k) : mul.comm
                  ... = n * gcd m k         : gcd_mul_left
                  ... = gcd m k * n         : mul.comm

theorem gcd_pos_of_pos_left {m : ℕ} (n : ℕ) (mpos : m > 0) : gcd m n > 0 :=
pos_of_dvd_of_pos !gcd_dvd_left mpos

theorem gcd_pos_of_pos_right (m : ℕ) {n : ℕ} (npos : n > 0) : gcd m n > 0 :=
pos_of_dvd_of_pos !gcd_dvd_right npos

theorem eq_zero_of_gcd_eq_zero_left {m n : ℕ} (H : gcd m n = 0) : m = 0 :=
or.elim (eq_zero_or_pos m)
  (assume H1, H1)
  (assume H1 : m > 0, absurd H⁻¹ (ne_of_lt (!gcd_pos_of_pos_left H1)))

theorem eq_zero_of_gcd_eq_zero_right {m n : ℕ} (H : gcd m n = 0) : n = 0 :=
eq_zero_of_gcd_eq_zero_left (!gcd.comm ▸ H)

theorem gcd_div {m n k : ℕ} (H1 : k ∣ m) (H2 : k ∣ n) :
  gcd (m div k) (n div k) = gcd m n div k :=
or.elim (eq_zero_or_pos k)
  (assume H3 : k = 0, by subst k; rewrite *div_zero)
  (assume H3 : k > 0, (div_eq_of_eq_mul_left H3 (calc
        gcd m n = gcd m (n div k * k)             : div_mul_cancel H2
            ... = gcd (m div k * k) (n div k * k) : div_mul_cancel H1
            ... = gcd (m div k) (n div k) * k     : gcd_mul_right))⁻¹)

theorem gcd_dvd_gcd_mul_left (m n k : ℕ) : gcd m n ∣ gcd (k * m) n :=
dvd_gcd (dvd.trans !gcd_dvd_left !dvd_mul_left) !gcd_dvd_right

theorem gcd_dvd_gcd_mul_right (m n k : ℕ) : gcd m n ∣ gcd (m * k) n :=
!mul.comm ▸ !gcd_dvd_gcd_mul_left

theorem gcd_dvd_gcd_mul_left_right (m n k : ℕ) : gcd m n ∣ gcd m (k * n) :=
dvd_gcd  !gcd_dvd_left (dvd.trans !gcd_dvd_right !dvd_mul_left)

theorem gcd_dvd_gcd_mul_right_right (m n k : ℕ) : gcd m n ∣ gcd m (n * k) :=
!mul.comm ▸ !gcd_dvd_gcd_mul_left_right

/- lcm -/

definition lcm (m n : ℕ) : ℕ := m * n div (gcd m n)

theorem lcm.comm (m n : ℕ) : lcm m n = lcm n m :=
calc
  lcm m n = m * n div gcd m n : rfl
      ... = n * m div gcd m n : mul.comm
      ... = n * m div gcd n m : gcd.comm
      ... = lcm n m           : rfl

theorem lcm_zero_left (m : ℕ) : lcm 0 m = 0 :=
calc
  lcm 0 m = 0 * m div gcd 0 m : rfl
      ... = 0 div gcd 0 m     : zero_mul
      ... = 0                 : zero_div

theorem lcm_zero_right (m : ℕ) : lcm m 0 = 0 := !lcm.comm ▸ !lcm_zero_left

theorem lcm_one_left (m : ℕ) : lcm 1 m = m :=
calc
  lcm 1 m = 1 * m div gcd 1 m : rfl
      ... = m div gcd 1 m     : one_mul
      ... = m div 1           : gcd_one_left
      ... = m                 : div_one

theorem lcm_one_right (m : ℕ) : lcm m 1 = m := !lcm.comm ▸ !lcm_one_left

theorem lcm_self (m : ℕ) : lcm m m = m :=
have H : m * m div m = m, from
  by_cases_zero_pos m !div_zero (take m, assume H1 : m > 0, !mul_div_cancel H1),
calc
  lcm m m = m * m div gcd m m : rfl
      ... = m * m div m       : gcd_self
      ... = m                 : H

theorem dvd_lcm_left (m n : ℕ) : m ∣ lcm m n :=
have H : lcm m n = m * (n div gcd m n), from mul_div_assoc _ !gcd_dvd_right,
dvd.intro H⁻¹

theorem dvd_lcm_right (m n : ℕ) : n ∣ lcm m n :=
!lcm.comm ▸ !dvd_lcm_left

theorem gcd_mul_lcm (m n : ℕ) : gcd m n * lcm m n = m * n :=
eq.symm (eq_mul_of_div_eq_right (dvd.trans !gcd_dvd_left !dvd_mul_right) rfl)

theorem lcm_dvd {m n k : ℕ} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k :=
or.elim (eq_zero_or_pos k)
  (assume kzero : k = 0, !kzero⁻¹ ▸ !dvd_zero)
  (assume kpos : k > 0,
    have mpos : m > 0, from pos_of_dvd_of_pos H1 kpos,
    have npos : n > 0, from pos_of_dvd_of_pos H2 kpos,
    have gcd_pos : gcd m n > 0, from !gcd_pos_of_pos_left mpos,
    obtain p (km : k = m * p), from exists_eq_mul_right_of_dvd H1,
    obtain q (kn : k = n * q), from exists_eq_mul_right_of_dvd H2,
    have ppos : p > 0, from pos_of_mul_pos_left (km ▸ kpos),
    have qpos : q > 0, from pos_of_mul_pos_left (kn ▸ kpos),
    have H3 : p * q * (m * n * gcd p q) = p * q * (gcd m n * k), from
    calc
      p * q * (m * n * gcd p q)
            = m * p * (n * q * gcd p q)       : by rewrite [*mul.assoc, *mul.left_comm q,
                                                             mul.left_comm p]
        ... = k * (k * gcd p q)               : by rewrite [-kn, -km]
        ... = k * gcd (k * p) (k * q)         : by rewrite gcd_mul_left
        ... = k * gcd (n * q * p) (m * p * q) : by rewrite [-kn, -km]
        ... = k * (gcd n m * (p * q))         : by rewrite [*mul.assoc, mul.comm q, gcd_mul_right]
        ... = p * q * (gcd m n * k)           : by rewrite [mul.comm, mul.comm (gcd n m), gcd.comm,
                                                             *mul.assoc],
    have H4 : m * n * gcd p q = gcd m n * k,
      from !eq_of_mul_eq_mul_left (mul_pos ppos qpos) H3,
    have H5 : gcd m n * (lcm m n * gcd p q) = gcd m n * k,
      from !mul.assoc ▸ !gcd_mul_lcm⁻¹ ▸ H4,
    have H6 : lcm m n * gcd p q = k,
      from !eq_of_mul_eq_mul_left gcd_pos H5,
    dvd.intro H6)

theorem lcm.assoc (m n k : ℕ) : lcm (lcm m n) k = lcm m (lcm n k) :=
dvd.antisymm
  (lcm_dvd
    (lcm_dvd !dvd_lcm_left (dvd.trans !dvd_lcm_left !dvd_lcm_right))
    (dvd.trans !dvd_lcm_right !dvd_lcm_right))
  (lcm_dvd
    (dvd.trans !dvd_lcm_left !dvd_lcm_left)
    (lcm_dvd (dvd.trans !dvd_lcm_right !dvd_lcm_left) !dvd_lcm_right))

/- coprime -/

definition coprime [reducible] (m n : ℕ) : Prop := gcd m n = 1

theorem coprime_swap {m n : ℕ} (H : coprime n m) : coprime m n :=
!gcd.comm ▸ H

theorem dvd_of_coprime_of_dvd_mul_right {m n k : ℕ} (H1 : coprime k n) (H2 : k ∣ m * n) : k ∣ m :=
have H3 : gcd (m * k) (m * n) = m, from
  calc
    gcd (m * k) (m * n) = m * gcd k n : gcd_mul_left
                    ... = m * 1       : H1
                    ... = m           : mul_one,
have H4 : (k ∣ gcd (m * k) (m * n)), from dvd_gcd !dvd_mul_left H2,
H3 ▸ H4

theorem dvd_of_coprime_of_dvd_mul_left {m n k : ℕ} (H1 : coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
dvd_of_coprime_of_dvd_mul_right H1 (!mul.comm ▸ H2)

theorem gcd_mul_left_cancel_of_coprime {k : ℕ} (m : ℕ) {n : ℕ} (H : coprime k n) :
   gcd (k * m) n = gcd m n :=
have H1 : coprime (gcd (k * m) n) k, from
  calc
    gcd (gcd (k * m) n) k
         = gcd (k * gcd 1 m) n : by rewrite [-gcd_mul_left, mul_one, gcd.comm, gcd.assoc]
     ... = 1                   : by rewrite [gcd_one_left, mul_one, ↑coprime at H, H],
dvd.antisymm
  (dvd_gcd (dvd_of_coprime_of_dvd_mul_left H1 !gcd_dvd_left) !gcd_dvd_right)
  (dvd_gcd (dvd.trans !gcd_dvd_left !dvd_mul_left) !gcd_dvd_right)

theorem gcd_mul_right_cancel_of_coprime (m : ℕ) {k n : ℕ} (H : coprime k n) :
   gcd (m * k) n = gcd m n :=
!mul.comm ▸ !gcd_mul_left_cancel_of_coprime H

theorem gcd_mul_left_cancel_of_coprime_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
   gcd m (k * n) = gcd m n :=
!gcd.comm ▸ !gcd.comm ▸ !gcd_mul_left_cancel_of_coprime H

theorem gcd_mul_right_cancel_of_coprime_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
   gcd m (n * k) = gcd m n :=
!gcd.comm ▸ !gcd.comm ▸ !gcd_mul_right_cancel_of_coprime H

theorem coprime_div_gcd_div_gcd {m n : ℕ} (H : gcd m n > 0) :
  coprime (m div gcd m n) (n div gcd m n) :=
calc
  gcd (m div gcd m n) (n div gcd m n) = gcd m n div gcd m n : gcd_div !gcd_dvd_left !gcd_dvd_right
     ... = 1 : div_self H

theorem exists_coprime {m n : ℕ} (H : gcd m n > 0) :
  exists m' n', coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
have H1 : m = (m div gcd m n) * gcd m n, from (div_mul_cancel !gcd_dvd_left)⁻¹,
have H2 : n = (n div gcd m n) * gcd m n, from (div_mul_cancel !gcd_dvd_right)⁻¹,
exists.intro _ (exists.intro _ (and.intro (coprime_div_gcd_div_gcd H) (and.intro H1 H2)))

theorem coprime_mul {m n k : ℕ} (H1 : coprime m k) (H2 : coprime n k) : coprime (m * n) k :=
calc
  gcd (m * n) k = gcd n k : !gcd_mul_left_cancel_of_coprime H1
            ... = 1       : H2

theorem coprime_mul_right {k m n : ℕ} (H1 : coprime k m) (H2 : coprime k n) : coprime k (m * n) :=
coprime_swap (coprime_mul (coprime_swap H1) (coprime_swap H2))

theorem coprime_of_coprime_mul_left {k m n : ℕ} (H : coprime (k * m) n) : coprime m n :=
have H1 : (gcd m n ∣ gcd (k * m) n), from !gcd_dvd_gcd_mul_left,
eq_one_of_dvd_one (H ▸ H1)

theorem coprime_of_coprime_mul_right {k m n : ℕ} (H : coprime (m * k) n) : coprime m n :=
coprime_of_coprime_mul_left (!mul.comm ▸ H)

theorem coprime_of_coprime_mul_left_right {k m n : ℕ} (H : coprime m (k * n)) : coprime m n :=
coprime_swap (coprime_of_coprime_mul_left (coprime_swap H))

theorem coprime_of_coprime_mul_right_right {k m n : ℕ} (H : coprime m (n * k)) : coprime m n :=
coprime_of_coprime_mul_left_right (!mul.comm ▸ H)

theorem comprime_one_left : ∀ n, coprime 1 n :=
λ n, !gcd_one_left

theorem comprime_one_right : ∀ n, coprime n 1 :=
λ n, !gcd_one_right

theorem exists_eq_prod_and_dvd_and_dvd {m n k} (H : k ∣ m * n) :
  ∃ m' n', k = m' * n' ∧ m' ∣ m ∧ n' ∣ n :=
or.elim (eq_zero_or_pos (gcd k m))
 (assume H1 : gcd k m = 0,
    have H2 : k = 0, from eq_zero_of_gcd_eq_zero_left H1,
    have H3 : m = 0, from eq_zero_of_gcd_eq_zero_right H1,
    have H4 : k = 0 * n, from H2 ⬝ !zero_mul⁻¹,
    have H5 : 0 ∣ m, from H3⁻¹ ▸ !dvd.refl,
    have H6 : n ∣ n, from !dvd.refl,
    exists.intro _ (exists.intro _ (and.intro H4 (and.intro H5 H6))))
  (assume H1 : gcd k m > 0,
    have H2 : gcd k m ∣ k, from !gcd_dvd_left,
    have H3 : k div gcd k m ∣ (m * n) div gcd k m, from div_dvd_div H2 H,
    have H4 : (m * n) div gcd k m = (m div gcd k m) * n, from
      calc
        m * n div gcd k m = n * m div gcd k m   : mul.comm
                      ... = n * (m div gcd k m) : !mul_div_assoc !gcd_dvd_right
                      ... = m div gcd k m * n   : mul.comm,
    have H5 : k div gcd k m ∣ (m div gcd k m) * n, from H4 ▸ H3,
    have H6 : coprime (k div gcd k m) (m div gcd k m), from coprime_div_gcd_div_gcd H1,
    have H7 : k div gcd k m ∣ n, from dvd_of_coprime_of_dvd_mul_left H6 H5,
    have H8 : k = gcd k m * (k div gcd k m), from (mul_div_cancel' H2)⁻¹,
    exists.intro _ (exists.intro _ (and.intro H8 (and.intro !gcd_dvd_right H7))))

end nat
