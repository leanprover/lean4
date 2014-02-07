-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import macros
import pair
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
      have   eq :   some a = none,
         from (symm N) ◂ (refl (@none B)),
      show false,
         from absurd eq (distinct a))

theorem inr_pred (A : (Type U)) {B : (Type U)} (b : B) : sum_pred A B (pair none (some b))
:= not_intro
     (assume N  : (none = (@none A)) = (some b = none),
      have   eq :   some b = none,
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
                      ... = proj1 (pair (some a2) (@none B))  : pair_inj1 rep_eq
                      ... = some a2                                     : refl (some a2))

theorem inr_inj {A B : (Type U)} {b1 b2 : B} : inr A b1 = inr A b2 → b1 = b2
:= assume Heq : inr A b1   = inr A b2,
     have eq1    :  inr A b1 = abst (pair none (some b1)) (inhabr A (inhabited_intro b1)),
        from refl (inr A b1),
     have eq2    :  inr A b2 = abst (pair none (some b2)) (inhabr A (inhabited_intro b1)),
        from subst (refl (inr A b2)) (proof_irrel (inhabr A (inhabited_intro b2)) (inhabr A (inhabited_intro b1))),
     have rep_eq : (pair none (some b1)) = (pair none (some b2)),
        from abst_inj (inhabr A (inhabited_intro b1)) (inr_pred A b1) (inr_pred A b2) (trans (trans (symm eq1) Heq) eq2),
     show b1 = b2,
        from optional::injectivity
            (calc some b1 = proj2 (pair (@none A) (some b1))  : refl (some b1)
                      ... = proj2 (pair (@none A) (some b2))  : pair_inj2 rep_eq
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
        from absurd (pair_inj1 rep_eq) (optional::distinct a)

set_opaque optional false
set_opaque subtype false
set_opaque optional::some false
set_opaque optional::none false
set_opaque subtype::rep false
set_opaque subtype::abst false
set_opaque optional_pred false

theorem dichotomy {A B : (Type U)} (n : sum A B) : (∃ a, n = inl a B) ∨ (∃ b, n = inr A b)
:= let pred : (proj1 (rep n) = none) ≠ (proj2 (rep n) = none) := P_rep n
   in _
