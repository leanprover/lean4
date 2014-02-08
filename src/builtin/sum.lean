-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import macros
import subtype
import optional
using subtype
using optional

-- We are encoding the (sum A B) as a subtype of (optional A) # (optional B), where
--    (proj1 n = none) ≠ (proj2 n = none)
definition sum_pred (A B : (Type U)) := λ p : (optional A) # (optional B), (proj1 p = none) ≠ (proj2 p = none)
definition sum (A B : (Type U)) := subtype ((optional A) # (optional B)) (sum_pred A B)

namespace sum
theorem inl_pred {A : (Type U)} (a : A) (B : (Type U)) : sum_pred A B (pair (some a) none)
:= not_intro
     (assume N  : (some a = none) = (none = (@none B)),
      have   eq : some a = none,
         from (symm N) ◂ (refl (@none B)),
      show false,
         from absurd eq (distinct a))

theorem inr_pred (A : (Type U)) {B : (Type U)} (b : B) : sum_pred A B (pair none (some b))
:= not_intro
     (assume N  : (none = (@none A)) = (some b = none),
      have   eq : some b = none,
         from N ◂ (refl (@none A)),
      show false,
        from absurd eq (distinct b))

theorem inhabl {A : (Type U)} (H : inhabited A) (B : (Type U)) : inhabited (sum A B)
:= inhabited_elim H (take w : A,
      subtype_inhabited (exists_intro (pair (some w) none) (inl_pred w B)))

theorem inhabr (A : (Type U)) {B : (Type U)} (H : inhabited B) : inhabited (sum A B)
:= inhabited_elim H (take w : B,
      subtype_inhabited (exists_intro (pair none (some w)) (inr_pred A w)))

definition inl {A : (Type U)} (a : A) (B : (Type U)) : sum A B
:= abst (pair (some a) none) (inhabl (inhabited_intro a) B)

definition inr (A : (Type U)) {B : (Type U)} (b : B) : sum A B
:= abst (pair none (some b)) (inhabr A (inhabited_intro b))

theorem inl_inj {A B : (Type U)} {a1 a2 : A} : inl a1 B = inl a2 B → a1 = a2
:= assume Heq : inl a1 B = inl a2 B,
     have eq1    : inl a1 B = abst (pair (some a1) none) (inhabl (inhabited_intro a1) B),
        from refl (inl a1 B),
     have eq2    : inl a2 B = abst (pair (some a2) none) (inhabl (inhabited_intro a1) B),
        from subst (refl (inl a2 B)) (proof_irrel (inhabl (inhabited_intro a2) B) (inhabl (inhabited_intro a1) B)),
     have rep_eq : (pair (some a1) none) = (pair (some a2) none),
        from abst_inj (inhabl (inhabited_intro a1) B) (inl_pred a1 B) (inl_pred a2 B) (trans (trans (symm eq1) Heq) eq2),
     show a1 = a2,
        from optional::injectivity
            (calc some a1 = proj1 (pair (some a1) (@none B))  : refl (some a1)
                      ... = proj1 (pair (some a2) (@none B))  : proj1_congr rep_eq
                      ... = some a2                           : refl (some a2))

theorem inr_inj {A B : (Type U)} {b1 b2 : B} : inr A b1 = inr A b2 → b1 = b2
:= assume Heq : inr A b1 = inr A b2,
     have eq1    :  inr A b1 = abst (pair none (some b1)) (inhabr A (inhabited_intro b1)),
        from refl (inr A b1),
     have eq2    :  inr A b2 = abst (pair none (some b2)) (inhabr A (inhabited_intro b1)),
        from subst (refl (inr A b2)) (proof_irrel (inhabr A (inhabited_intro b2)) (inhabr A (inhabited_intro b1))),
     have rep_eq : (pair none (some b1)) = (pair none (some b2)),
        from abst_inj (inhabr A (inhabited_intro b1)) (inr_pred A b1) (inr_pred A b2) (trans (trans (symm eq1) Heq) eq2),
     show b1 = b2,
        from optional::injectivity
            (calc some b1 = proj2 (pair (@none A) (some b1))  : refl (some b1)
                      ... = proj2 (pair (@none A) (some b2))  : proj2_congr rep_eq
                      ... = some b2                           : refl (some b2))

theorem distinct {A B : (Type U)} (a : A) (b : B) : inl a B ≠ inr A b
:= assume N : inl a B = inr A b,
     have eq1   : inl a B = abst (pair (some a) none) (inhabl (inhabited_intro a) B),
        from refl (inl a B),
     have eq2   : inr A b = abst (pair none (some b)) (inhabl (inhabited_intro a) B),
        from subst (refl (inr A b)) (proof_irrel (inhabr A (inhabited_intro b)) (inhabl (inhabited_intro a) B)),
     have rep_eq : (pair (some a) none) = (pair none (some b)),
        from abst_inj (inhabl (inhabited_intro a) B) (inl_pred a B) (inr_pred A b) (trans (trans (symm eq1) N) eq2),
     show false,
        from absurd (proj1_congr rep_eq) (optional::distinct a)

theorem dichotomy {A B : (Type U)} (n : sum A B) : (∃ a, n = inl a B) ∨ (∃ b, n = inr A b)
:= let pred : (proj1 (rep n) = none) ≠ (proj2 (rep n) = none) := P_rep n
   in or_elim (em (proj1 (rep n) = none))
         (assume Heq : proj1 (rep n) = none,
          have neq_none : ¬ proj2 (rep n) = (@none B),
             from (symm (not_iff_elim (ne_symm pred))) ◂ Heq,
          have ex_some  : ∃ b, proj2 (rep n) = some b,
             from resolve1 (optional::dichotomy (proj2 (rep n))) neq_none,
          obtain (b : B) (Hb : proj2 (rep n) = some b),
             from ex_some,
          show (∃ a, n = inl a B) ∨ (∃ b, n = inr A b),
             from or_intror (∃ a, n = inl a B)
                (have rep_eq   : rep n         = pair none (some b),
                    from pairext_proj Heq Hb,
                 have rep_inr  : rep (inr A b) = pair none (some b),
                    from rep_abst (inhabr A (inhabited_intro b)) (pair none (some b)) (inr_pred A b),
                 have n_eq_inr : n = inr A b,
                    from rep_inj (trans rep_eq (symm rep_inr)),
                 show (∃ b, n = inr A b),
                    from exists_intro b n_eq_inr))
         (assume Hne : ¬ proj1 (rep n) = none,
          have eq_none : proj2 (rep n) = (@none B),
             from (not_iff_elim pred) ◂ Hne,
          have ex_some : ∃ a, proj1 (rep n) = some a,
             from resolve1 (optional::dichotomy (proj1 (rep n))) Hne,
          obtain (a : A) (Ha : proj1 (rep n) = some a),
             from ex_some,
          show (∃ a, n = inl a B) ∨ (∃ b, n = inr A b),
            from or_introl
               (have rep_eq   : rep n  = pair (some a) none,
                   from pairext_proj Ha eq_none,
                have rep_inl  : rep (inl a B) = pair (some a) none,
                   from rep_abst (inhabl (inhabited_intro a) B) (pair (some a) none) (inl_pred a B),
                have n_eq_inl : n = inl a B,
                   from rep_inj (trans rep_eq (symm rep_inl)),
                show ∃ a, n = inl a B,
                   from exists_intro a n_eq_inl)
                (∃ b, n = inr A b))

theorem induction {A B : (Type U)} {P : sum A B → Bool} (H1 : ∀ a, P (inl a B)) (H2 : ∀ b, P (inr A b)) : ∀ n, P n
:= take n, or_elim (sum::dichotomy n)
    (assume Hex : ∃ a, n = inl a B,
     obtain (a : A) (Ha : n = inl a B), from Hex,
     show P n,
        from subst (H1 a) (symm Ha))
    (assume Hex : ∃ b, n = inr A b,
     obtain (b : B) (Hb : n = inr A b), from Hex,
     show P n,
        from subst (H2 b) (symm Hb))

set_opaque inl true
set_opaque inr true
end
set_opaque sum_pred true
set_opaque sum      true
