----------------------------------------------------------------------------------------------------
--
-- theory primes.lean
-- author: Jeremy Avigad
--
-- Experimenting with Lean.
--
----------------------------------------------------------------------------------------------------

import macros
import tactic
using Nat

--
-- fundamental properties of Nat
--

theorem cases_on {P : Nat → Bool} (a : Nat) (H1 : P 0) (H2 : ∀ (n : Nat), P (n + 1)) : P a
:= induction_on a H1 (take n : Nat, assume ih : P n, H2 n)

theorem strong_induction_on {P : Nat → Bool} (a : Nat) (H : ∀ n, (∀ m, m < n → P m) → P n) : P a
:= @strong_induction P H a

-- in hindsight, now I know I don't need these
theorem one_ne_zero : 1 ≠ 0 := succ_nz 0
theorem two_ne_zero : 2 ≠ 0 := succ_nz 1

--
-- observation: the proof of lt_le_trans in Nat is not needed
--

theorem lt_le_trans2 {a b c : Nat} (H1 : a < b) (H2 : b ≤ c) : a < c
:= le_trans H1 H2

--
-- also, contrapos and mt are the same theorem
--

theorem contrapos2 {a b : Bool} (H : a → b) : ¬ b → ¬ a
:= mt H

--
-- properties of lt and le
--

theorem succ_le_succ {a b : Nat} (H : a + 1 ≤ b + 1) : a ≤ b
:=
  obtain (x : Nat) (Hx : a + 1 + x = b + 1), from lt_elim H,
  have H2 : a + x + 1 = b + 1, from (calc
    a + x + 1 = a + (x + 1) : add_assoc _ _ _
          ... = a + (1 + x) : { add_comm x 1 }
          ... = a + 1 + x : symm (add_assoc _ _ _)
          ... = b + 1 : Hx),
  have H3 : a + x = b, from (succ_inj H2),
  show a ≤ b, from (le_intro H3)

-- should we keep this duplication or < and <=?
theorem lt_succ {a b : Nat} (H : a < b + 1) : a ≤ b
:= succ_le_succ H

theorem succ_le_succ_eq (a b : Nat) : a + 1 ≤ b + 1 ↔ a ≤ b
:= iff_intro succ_le_succ (assume H : a ≤ b, le_add H 1)

theorem lt_succ_eq (a b : Nat) : a < b + 1 ↔ a ≤ b
:= succ_le_succ_eq a b

theorem le_or_lt (a : Nat) : ∀ b : Nat, a ≤ b ∨ b < a
:=
  induction_on a (
    show ∀b, 0 ≤ b ∨ b < 0,
      from take b, or_introl (le_zero b) _
  ) (
    take a,
    assume ih : ∀b, a ≤ b ∨ b < a,
    show ∀b, a + 1 ≤ b ∨ b < a + 1,
      from
        take b,
        cases_on b (
          show a + 1 ≤ 0 ∨ 0 < a + 1,
            from or_intror _ (le_add (le_zero a) 1)
        ) (
          take b,
          have H : a ≤ b ∨ b < a, from ih b,
          show a + 1 ≤ b + 1 ∨ b + 1 < a + 1,
            from or_elim H (
              assume H1 : a ≤ b,
                or_introl (le_add H1 1) (b + 1 < a + 1)
            ) (
              assume H2 : b < a,
                or_intror (a + 1 ≤ b + 1) (le_add H2 1)
            )
        )
  )

theorem not_le_lt {a b : Nat} : ¬ a ≤ b → b < a
:= (or_imp _ _) ◂ le_or_lt a b

theorem not_lt_le {a b : Nat} : ¬ a < b → b ≤ a
:= (or_imp _ _) ◂ (or_comm _ _ ◂ le_or_lt b a)

theorem lt_not_le {a b : Nat} (H : a < b) : ¬ b ≤ a
:= not_intro (take H1 : b ≤ a, absurd (lt_le_trans H H1) (lt_nrefl a))

theorem le_not_lt {a b : Nat} (H : a ≤ b) : ¬ b < a
:= not_intro (take H1 : b < a, absurd H (lt_not_le H1))

theorem not_le_iff {a b : Nat} : ¬ a ≤ b ↔ b < a
:= iff_intro (@not_le_lt a b) (@lt_not_le b a)

theorem not_lt_iff {a b : Nat} : ¬ a < b ↔ b ≤ a
:= iff_intro (@not_lt_le a b) (@le_not_lt b a)

theorem le_iff {a b : Nat} : a ≤ b ↔ a < b ∨ a = b
:=
  iff_intro (
    assume H : a ≤ b,
    show a < b ∨ a = b,
      from or_elim (em (a = b)) (
        take H1 : a = b,
        show a < b ∨ a = b, from or_intror _ H1
      ) (
        take H2 : a ≠ b,
        have H3 : ¬ b ≤ a,
          from not_intro (take H4: b ≤ a, absurd (le_antisym H H4) H2),
        have H4 : a < b, from resolve1 (le_or_lt b a) H3,
        show a < b ∨ a = b, from or_introl H4 _
      )
  )(
    assume H : a < b ∨ a = b,
    show a ≤ b,
      from or_elim H (
        take H1 : a < b, lt_le H1
      ) (
        take H1 : a = b, subst (le_refl a) H1
      )
  )

theorem ne_symm_iff {A : (Type U)} (a b : A) : a ≠ b ↔ b ≠ a
:= iff_intro ne_symm ne_symm

theorem lt_iff (a b : Nat) : a < b ↔ a ≤ b ∧ a ≠ b
:=
  calc
    a < b = ¬ b ≤ a            : symm (not_le_iff)
       ... = ¬ (b < a ∨ b = a) : { le_iff }
       ... = ¬ b < a ∧ b ≠ a   : not_or _ _
       ... = a ≤ b ∧ b ≠ a     : { not_lt_iff }
       ... = a ≤ b ∧ a ≠ b     : { ne_symm_iff _ _ }

theorem ne_zero_ge_one {x : Nat} (H : x ≠ 0) : x ≥ 1
:= resolve2 (le_iff ◂ (le_zero x)) (ne_symm H)

theorem ne_zero_one_ge_two {x : Nat} (H0 : x ≠ 0) (H1 : x ≠ 1) : x ≥ 2
:= resolve2 (le_iff ◂ (ne_zero_ge_one H0)) (ne_symm H1)

-- the forward direction can be replaced by ne_zero_ge_one, but
-- note the comments below
theorem ne_zero_iff (n : Nat) : n ≠ 0 ↔ n > 0
:=
  iff_intro (
    assume H : n ≠ 0,
    by_contradiction (
      assume H1 : ¬ n > 0,
      -- curious: if you make the arguments implicit in the next line,
      -- it fails (the evaluator is getting in the way, I think)
      have H2 : n = 0, from le_antisym (@not_lt_le 0 n H1) (le_zero n),
      absurd H2 H
    )
  ) (
    -- here too
    assume H : n > 0, ne_symm (@lt_ne 0 n H)
  )

-- Note: this differs from Leo's naming conventions
theorem mul_right_mono {x y : Nat} (H : x ≤ y) (z : Nat) : x * z ≤ y * z
:=
  obtain (w : Nat) (Hw : x + w = y),
    from le_elim H,
  le_intro (
    show x * z + w * z = y * z,
      from calc
        x * z + w * z = (x + w) * z : symm (distributel x w z)
                  ... = y * z       : { Hw }
  )

theorem mul_left_mono (x : Nat) {y z : Nat} (H : y ≤ z) : x * y ≤ x * z
:= subst (subst (mul_right_mono H x) (mul_comm y x)) (mul_comm z x)

theorem le_addr (a b : Nat) : a ≤ a + b
:= le_intro (refl (a + b))

theorem le_addl (a b : Nat) : a ≤ b + a
:= subst (le_addr a b) (add_comm a b)

theorem add_left_mono {a b : Nat} (c : Nat) (H : a ≤ b) : c + a ≤ c + b
:=  subst (subst (le_add H c) (add_comm a c)) (add_comm b c)

theorem mul_right_strict_mono {x y z : Nat} (H : x < y) (znez : z ≠ 0) : x * z < y * z
:=
  obtain (w : Nat) (Hw : x + 1 + w = y),
    from le_elim H,
  have H1 : y * z = x * z + w * z + z,
    from calc
      y * z = (x + 1 + w) * z      : { symm Hw }
        ... = (x + (1 + w)) * z    : { add_assoc _ _ _ }
        ... = (x + (w + 1)) * z    : { add_comm _ _ }
        ... = (x + w + 1) * z      : { symm (add_assoc _ _ _) }
        ... = (x + w) * z + 1 * z  : distributel _ _ _
        ... = (x + w) * z + z      : { mul_onel _ }
        ... = x * z + w * z + z    : { distributel _ _ _ },
  have H2 : x * z ≤ x * z + w * z, from le_addr _ _,
  have H3 : x * z + w * z < x * z + w * z + z, from add_left_mono _ (ne_zero_ge_one znez),
  show x * z < y * z, from subst (le_lt_trans H2 H3) (symm H1)

theorem mul_left_strict_mono {x y z : Nat} (H : x < y) (znez : z ≠ 0) : z * x < z * y
:= subst (subst (mul_right_strict_mono H znez) (mul_comm x z)) (mul_comm y z)

theorem mul_left_le_cancel {a b c : Nat} (H : a * b ≤ a * c) (anez : a ≠ 0) : b ≤ c
:=
  by_contradiction (
    assume H1 : ¬ b ≤ c,
    have H2 : a * c < a * b, from mul_left_strict_mono (not_le_lt H1) anez,
    show false, from absurd H (lt_not_le H2)
  )

theorem mul_right_le_cancel {a b c : Nat} (H : b * a ≤ c * a) (anez : a ≠ 0) : b ≤ c
:= mul_left_le_cancel (subst (subst H (mul_comm b a)) (mul_comm c a)) anez

theorem mul_left_lt_cancel {a b c : Nat} (H : a * b < a * c) : b < c
:=
  by_contradiction (
    assume H1 : ¬ b < c,
    have H2 : a * c ≤ a * b, from mul_left_mono a (not_lt_le H1),
    show false, from absurd H (le_not_lt H2)
  )

theorem mul_right_lt_cancel {a b c : Nat} (H : b * a < c * a) : b < c
:= mul_left_lt_cancel (subst (subst H (mul_comm b a)) (mul_comm c a))

theorem add_right_comm (a b c : Nat) : a + b + c = a + c + b
:=
  calc
    a + b + c = a + (b + c) : add_assoc _ _ _
          ... = a + (c + b) : { add_comm b c }
          ... = a + c + b   : symm (add_assoc _ _ _)

theorem add_left_le_cancel {a b c : Nat} (H : a + c ≤ b + c) : a ≤ b
:=
  obtain (d : Nat) (Hd : a + c + d = b + c), from le_elim H,
  le_intro (add_injl (subst Hd (add_right_comm a c d)))

theorem add_right_le_cancel {a b c : Nat} (H : c + a ≤ c + b) : a ≤ b
:= add_left_le_cancel (subst (subst H (add_comm c a)) (add_comm c b))

--
-- more properties of multiplication
--

theorem mul_left_cancel {a b c : Nat} (H : a * b = a * c) (anez : a ≠ 0) : b = c
:=
  have H1 : a * b ≤ a * c, from subst (le_refl _) H,
  have H2 : a * c ≤ a * b, from subst (le_refl _) H,
  le_antisym (mul_left_le_cancel H1 anez) (mul_left_le_cancel H2 anez)

theorem mul_right_cancel {a b c : Nat} (H : b * a = c * a) (anez : a ≠ 0) : b = c
:= mul_left_cancel (subst (subst H (mul_comm b a)) (mul_comm c a)) anez


--
-- divisibility
--

definition dvd (a b : Nat) : Bool := ∃ c, a * c = b

infix 50 | : dvd

theorem dvd_intro {a b c : Nat} (H : a * c = b) : a | b
:= exists_intro c H

theorem dvd_elim {a b : Nat} (H : a | b) : ∃ c, a * c = b
:= H

theorem dvd_self (n : Nat) : n | n := dvd_intro (mul_oner n)

theorem one_dvd (a : Nat) : 1 | a
:= dvd_intro (mul_onel a)

theorem zero_dvd {a : Nat} (H: 0 | a) : a = 0
:=
  obtain (w : Nat) (H1 : 0 * w = a), from H,
    subst (symm H1) (mul_zerol _)

theorem dvd_zero (a : Nat) : a | 0
:= exists_intro 0 (mul_zeror _)

theorem dvd_trans {a b c} (H1 : a | b) (H2 : b | c) : a | c
:=
  obtain (w1 : Nat) (Hw1 : a * w1 = b), from H1,
  obtain (w2 : Nat) (Hw2 : b * w2 = c), from H2,
    exists_intro (w1 * w2)
      calc a * (w1 * w2) = a * w1 * w2 : symm (mul_assoc a w1 w2)
                     ... = b * w2 : { Hw1 }
                     ... = c : Hw2

theorem dvd_le {x y : Nat} (H : x | y) (ynez : y ≠ 0) : x ≤ y
:=
  obtain (w : Nat) (Hw : x * w = y), from H,
  have wnez : w ≠ 0, from
    not_intro (take H1 : w = 0, absurd (
      calc y = x * w : symm Hw
         ... = x * 0 : { H1 }
         ... = 0     : mul_zeror x
    ) ynez),
  have H2 : x * 1 ≤ x * w, from mul_left_mono x (ne_zero_ge_one wnez),
  show x ≤ y, from subst (subst H2 (mul_oner x)) Hw

theorem dvd_mul_right {a b : Nat} (H : a | b) (c : Nat) : a | b * c
:=
  obtain (d : Nat) (Hd : a * d = b), from dvd_elim H,
  dvd_intro (
    calc
      a * (d * c) = (a * d) * c : symm (mul_assoc _ _ _)
              ... = b * c       : { Hd }
  )

theorem dvd_mul_left {a b : Nat} (H : a | b) (c : Nat) : a | c * b
:= subst (dvd_mul_right H c) (mul_comm b c)

theorem dvd_add {a b c : Nat} (H1 : a | b) (H2 : a | c) : a | b + c
:=
  obtain (w1 : Nat) (Hw1 : a * w1 = b), from H1,
  obtain (w2 : Nat) (Hw2 : a * w2 = c), from H2,
    exists_intro (w1 + w2)
      calc a * (w1 + w2) = a * w1 + a * w2 : distributer _ _ _
                     ... = b + a * w2 : { Hw1 }
                     ... = b + c : { Hw2 }

theorem dvd_add_cancel {a b c : Nat} (H1 : a | b + c) (H2 : a | b) : a | c
:=
  or_elim (em (a = 0)) (
    assume az : a = 0,
    have H3 : c = 0, from
      calc c = 0 + c : symm (add_zerol _)
         ... = b + c : { symm (zero_dvd (subst H2 az)) }
         ... = 0     : zero_dvd (subst H1 az),
    show a | c, from subst (dvd_zero a) (symm H3)
  ) (
    assume anz : a ≠ 0,
    obtain (w1 : Nat) (Hw1 : a * w1 = b + c), from H1,
    obtain (w2 : Nat) (Hw2 : a * w2 = b), from H2,
    have H3 : a * w1 = a * w2 + c, from subst Hw1 (symm Hw2),
    have H4 : a * w2 ≤ a * w1, from le_intro (symm H3),
    have H5 : w2 ≤ w1, from mul_left_le_cancel H4 anz,
    obtain (w3 : Nat) (Hw3 : w2 + w3 = w1), from le_elim H5,
    have H6 : b + a * w3 = b + c, from
      calc
        b + a * w3 = a * w2 + a * w3 : { symm Hw2 }
               ... = a * (w2 + w3)   : symm (distributer _ _ _)
               ... = a * w1          : { Hw3 }
               ... = b + c           : Hw1,
    have H7 : a * w3 = c, from add_injr H6,
    show a | c, from dvd_intro H7
  )

--
-- primes
--

definition prime p := p ≥ 2 ∧ forall m, m | p → m = 1 ∨ m = p

theorem not_prime_has_divisor {n : Nat} (H1 : n ≥ 2) (H2 : ¬ prime n) : ∃ m, m | n ∧ m ≠ 1 ∧ m ≠ n
:=
  have H3 : ¬ n ≥ 2 ∨ ¬ (∀ m : Nat, m | n → m = 1 ∨ m = n),
    from not_and _ _ ◂ H2,
  have H4 : ¬ ¬ n ≥ 2,
    from (symm (not_not_eq _)) ◂ H1,
  obtain (m : Nat) (H5 :  ¬ (m | n → m = 1 ∨ m = n)),
    from not_forall_elim (resolve1 H3 H4),
  have H6 : m | n ∧ ¬ (m = 1 ∨ m = n),
    from (not_implies _ _) ◂ H5,
  have H7 : ¬ (m = 1 ∨ m = n) ↔ (m ≠ 1 ∧ m ≠ n),
    from not_or (m = 1) (m = n),
  have H8 : m | n ∧ m ≠ 1 ∧ m ≠ n,
    from subst H6 H7,
  show ∃ m, m | n ∧ m ≠ 1 ∧ m ≠ n,
    from exists_intro m H8

theorem not_prime_has_divisor2 {n : Nat} (H1 : n ≥ 2) (H2 : ¬ prime n) :
  ∃ m, m | n ∧ m ≥ 2 ∧ m < n
:=
  have n_ne_0 : n ≠ 0, from
    not_intro (take n0 : n = 0, substp (fun n, n ≥ 2) H1 n0),
  obtain (m : Nat) (Hm : m | n ∧ m ≠ 1 ∧ m ≠ n),
    from not_prime_has_divisor H1 H2,
  let m_dvd_n := and_eliml Hm in
  let m_ne_1 := and_eliml (and_elimr Hm) in
  let m_ne_n := and_elimr (and_elimr Hm) in
  have m_ne_0 : m ≠ 0, from
    not_intro (
      take m0 : m = 0,
      have n0 : n = 0, from zero_dvd (subst m_dvd_n m0),
      absurd n0 n_ne_0
    ),
  exists_intro m (
    and_intro m_dvd_n (
      and_intro (
        show m ≥ 2, from ne_zero_one_ge_two m_ne_0 m_ne_1
      ) (
        have m_le_n : m ≤ n, from dvd_le m_dvd_n n_ne_0,
        show m < n, from resolve2 (le_iff ◂ m_le_n) m_ne_n
      )
    )
  )

theorem has_prime_divisor {n : Nat} : n ≥ 2 → ∃ p, prime p ∧ p | n
:=
  strong_induction_on n (
    take n,
    assume ih : ∀ m, m < n → m ≥ 2 → ∃ p, prime p ∧ p | m,
    assume n_ge_2 : n ≥ 2,
    show ∃ p, prime p ∧ p | n, from
      or_elim (em (prime n)) (
        assume H : prime n,
        exists_intro n (and_intro H (dvd_self n))
      ) (
        assume H : ¬ prime n,
        obtain (m : Nat) (Hm : m | n ∧ m ≥ 2 ∧ m < n),
          from not_prime_has_divisor2 n_ge_2 H,
        obtain (p : Nat) (Hp : prime p ∧ p | m),
          from ih m (and_elimr (and_elimr Hm)) (and_eliml (and_elimr Hm)),
        have p_dvd_n : p | n, from dvd_trans (and_elimr Hp) (and_eliml Hm),
        exists_intro p (and_intro (and_eliml Hp) p_dvd_n)
      )
  )

--
-- factorial
--

variable fact : Nat → Nat

axiom fact_0 : fact 0 = 1

axiom fact_succ : ∀ n, fact (n + 1) = (n + 1) * fact n

-- can the simplifier do this?
theorem fact_1 : fact 1 = 1
:=
  calc
    fact 1 = fact (0 + 1)       : { symm (add_zerol 1) }
       ... = (0 + 1) * fact 0   : fact_succ _
       ... = 1 * fact 0         : { add_zerol 1 }
       ... = 1 * 1              : { fact_0 }
       ... = 1                  : mul_oner _

theorem fact_ne_0 (n : Nat) : fact n ≠ 0
:=
  induction_on n (
    not_intro (
      assume H : fact 0 = 0,
      have H1 : 1 = 0, from (subst H fact_0),
      absurd H1 one_ne_zero
    )
  ) (
    take n,
    assume ih : fact n ≠ 0,
    not_intro (
      assume H : fact (n + 1) = 0,
      have H1 : n + 1 = 0, from
        mul_right_cancel (
          calc
            (n + 1) * fact n = fact (n + 1) : symm (fact_succ n)
                         ... = 0            : H
                         ... = 0 * fact n   : symm (mul_zerol _)
        ) ih,
      absurd H1 (succ_nz _)
    )
  )

theorem dvd_fact {m n : Nat} (m_gt_0 : m > 0) (m_le_n : m ≤ n) : m | fact n
:=
  obtain (m' : Nat) (Hm' : 1 + m' = m), from le_elim m_gt_0,
  obtain (n' : Nat) (Hn' : 1 + n' = n), from le_elim (le_trans m_gt_0 m_le_n),
  have m'_le_n' : m' ≤ n',
    from add_right_le_cancel (subst (subst m_le_n (symm Hm')) (symm Hn')),
  have H : ∀ n' m', m' ≤ n' → m' + 1 | fact (n' + 1), from
    induction (
      take m' ,
      assume m'_le_0 : m' ≤ 0,
      have Hm' : m' + 1 = 1,
        from calc
          m' + 1 = 0 + 1 : { le_antisym m'_le_0 (le_zero m') }
             ... = 1     : add_zerol _,
      show m' + 1 | fact (0 + 1), from subst (one_dvd _) (symm Hm')
    ) (
      take n',
      assume ih : ∀m', m' ≤ n' → m' + 1 | fact (n' + 1),
      take m',
      assume Hm' : m' ≤ n' + 1,
      have H1 : m' < n' + 1 ∨ m' = n' + 1, from le_iff ◂ Hm',
      or_elim H1 (
        assume H2 : m' < n' + 1,
        have H3 : m' ≤ n', from lt_succ H2,
        have H4 : m' + 1 | fact (n' + 1), from ih _ H3,
        have H5 : m' + 1 | (n' + 1 + 1) * fact (n' + 1), from dvd_mul_left H4 _,
        show m' + 1 | fact (n' + 1 + 1), from subst H5 (symm (fact_succ _))
      ) (
        assume H2 : m' = n' + 1,
        have H3 : m' + 1 | n' + 1 + 1, from subst (dvd_self _) H2,
        have H4 : m' + 1 | (n' + 1 + 1) * fact (n' + 1), from dvd_mul_right H3 _,
        show m' + 1 | fact (n' + 1 + 1), from subst H4 (symm (fact_succ _))
      )
    ),
  have H1 : m' + 1 | fact (n' + 1), from H _ _ m'_le_n',
  show m | fact n,
    from (subst (subst (subst (subst H1 (add_comm m' 1)) Hm') (add_comm n' 1)) Hn')

theorem primes_infinite (n : Nat) : ∃ p, p ≥ n ∧ prime p
:=
  let m := fact (n + 1) in
  have Hn1 : n + 1 ≥ 1, from le_addl _ _,
  have m_ge_1 : m ≥ 1, from ne_zero_ge_one (fact_ne_0 _),
  have m1_ge_2 : m + 1 ≥ 2, from le_add m_ge_1 1,
  obtain (p : Nat) (Hp : prime p ∧ p | m + 1), from has_prime_divisor m1_ge_2,
  let prime_p := and_eliml Hp in
  let p_dvd_m1 := and_elimr Hp in
  have p_ge_2 : p ≥ 2, from and_eliml prime_p,
  have two_gt_0 : 2 > 0, from (ne_zero_iff 2) ◂ (succ_nz 1),
  -- fails if arguments are left implicit
  have p_gt_0 : p > 0, from @lt_le_trans 0 2 p two_gt_0 p_ge_2,
  have p_ge_n : p ≥ n, from
    by_contradiction (
      assume H1 : ¬ p ≥ n,
      have H2 : p < n, from not_le_lt H1,
      have H3 : p ≤ n + 1, from lt_le (lt_le_trans H2 (le_addr n 1)),
      have H4 : p | m, from dvd_fact p_gt_0 H3,
      have H5 : p | 1, from dvd_add_cancel p_dvd_m1 H4,
      have H6 : p ≤ 1, from dvd_le H5 (succ_nz 0),
      have H7 : 2 ≤ 1, from le_trans p_ge_2 H6,
      absurd H7 (lt_nrefl 1)
    ),
  exists_intro p (and_intro p_ge_n prime_p)
