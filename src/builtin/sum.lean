-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import macros
import subtype
import optional
using subtype
using optional
-- We are encoding the (sum A B) as a subtype of (optional A) ⨯ (optional B), where
--    (proj1 n = none) ≠ (proj2 n = none)
definition sum_pred (A B : (Type U)) := λ p : (optional A) ⨯ (optional B), (proj1 p = none) ≠ (proj2 p = none)
definition sum (A B : (Type U)) := subtype ((optional A) ⨯ (optional B)) (sum_pred A B)

namespace sum
-- TODO: move pair, pair_inj1 and pair_inj2 to separate file
definition pair {A : (Type U)} {B : (Type U)} (a : A) (b : B) := tuple a, b
theorem    pair_inj1 {A : (Type U)} {B : A → (Type U)} {a b : sig x, B x} (H : a = b) : proj1 a = proj1 b
:= subst (refl (proj1 a)) H
theorem    pair_inj2 {A B : (Type U)} {a b : A ⨯ B} (H : a = b) : proj2 a = proj2 b
:= subst (refl (proj2 a)) H
theorem    pairext_proj {A B : (Type U)} {p : A ⨯ B} {a : A} {b : B} (H1 : proj1 p = a) (H2 : proj2 p = b) : p = (pair a b)
:= @pairext A (λ x, B) p (pair a b) H1 (to_heq H2)

theorem inl_pred {A : (Type U)} (a : A) (B : (Type U)) : sum_pred A B (pair (some a) none)
:= not_intro
     (λ N : (some a = none) = (none = (optional::@none B)),
        let eq  :   some a = none := (symm N) ◂ (refl (optional::@none B))
        in absurd eq (distinct a))

theorem inr_pred (A : (Type U)) {B : (Type U)} (b : B) : sum_pred A B (pair none (some b))
:= not_intro
     (λ N : (none = (optional::@none A)) = (some b = none),
        let eq  :   some b = none := N ◂ (refl (optional::@none A))
        in absurd eq (distinct b))

theorem inhabl {A : (Type U)} (H : inhabited A) (B : (Type U)) : inhabited (sum A B)
:= inhabited_elim H (λ w : A,
      subtype_inhabited (exists_intro (pair (some w) none) (inl_pred w B)))

theorem inhabr (A : (Type U)) {B : (Type U)} (H : inhabited B) : inhabited (sum A B)
:= inhabited_elim H (λ w : B,
      subtype_inhabited (exists_intro (pair none (some w)) (inr_pred A w)))

definition inl {A : (Type U)} (a : A) (B : (Type U)) : sum A B
:= abst (pair (some a) none) (inhabl (inhabited_intro a) B)

definition inr (A : (Type U)) {B : (Type U)} (b : B) : sum A B
:= abst (pair none (some b)) (inhabr A (inhabited_intro b))

theorem inl_inj {A : (Type U)} (a1 a2 : A) (B : (Type U)) : inl a1 B = inl a2 B → a1 = a2
:= assume Heq : inl a1 B = inl a2 B,
     let eq1    : inl a1 B = abst (pair (some a1) none) (inhabl (inhabited_intro a1) B) := refl (inl a1 B),
         eq2    : inl a2 B = abst (pair (some a2) none) (inhabl (inhabited_intro a1) B)
                := subst (refl (inl a2 B)) (proof_irrel (inhabl (inhabited_intro a2) B) (inhabl (inhabited_intro a1) B)),
         rep_eq : (pair (some a1) none) = (pair (some a2) none)
                := abst_inj (inhabl (inhabited_intro a1) B) (inl_pred a1 B) (inl_pred a2 B) (trans (trans (symm eq1) Heq) eq2)
     in optional::injectivity
            (calc some a1 = proj1 (pair (some a1) (optional::@none B))  : refl (some a1)
                      ... = proj1 (pair (some a2) (optional::@none B))  : pair_inj1 rep_eq
                      ... = some a2                                     : refl (some a2))

theorem inr_inj (A : (Type U)) {B : (Type U)} (b1 b2 : B) : inr A b1 = inr A b2 → b1 = b2
:= assume Heq : inr A b1   = inr A b2,
     let eq1    : inr A b1 = abst (pair none (some b1)) (inhabr A (inhabited_intro b1)) := refl (inr A b1),
         eq2    : inr A b2 = abst (pair none (some b2)) (inhabr A (inhabited_intro b1))
                := subst (refl (inr A b2)) (proof_irrel (inhabr A (inhabited_intro b2)) (inhabr A (inhabited_intro b1))),
         rep_eq : (pair none (some b1)) = (pair none (some b2))
                := abst_inj (inhabr A (inhabited_intro b1)) (inr_pred A b1) (inr_pred A b2) (trans (trans (symm eq1) Heq) eq2)
     in optional::injectivity
            (calc some b1 = proj2 (pair (optional::@none A) (some b1))  : refl (some b1)
                      ... = proj2 (pair (optional::@none A) (some b2))  : pair_inj2 rep_eq
                      ... = some b2                                     : refl (some b2))

theorem distinct {A B : (Type U)} (a : A) (b : B) : inl a B ≠ inr A b
:= assume N : inl a B = inr A b,
     let eq1    : inl a B = abst (pair (some a) none) (inhabl (inhabited_intro a) B) := refl (inl a B),
         eq2    : inr A b = abst (pair none (some b)) (inhabl (inhabited_intro a) B)
                := subst (refl (inr A b)) (proof_irrel (inhabr A (inhabited_intro b)) (inhabl (inhabited_intro a) B)),
         rep_eq : (pair (some a) none) = (pair none (some b))
                := abst_inj (inhabl (inhabited_intro a) B) (inl_pred a B) (inr_pred A b) (trans (trans (symm eq1) N) eq2)
     in absurd (pair_inj1 rep_eq) (optional::distinct a)

theorem dichotomy {A B : (Type U)} (n : sum A B) : (∃ a, n = inl a B) ∨ (∃ b, n = inr A b)
:= let pred : (proj1 (rep n) = none) ≠ (proj2 (rep n) = none) := P_rep n
   in or_elim (em (proj1 (rep n) = none))
         (λ Heq,  let neq_none : ¬ proj2 (rep n) = (optional::@none B) := (symm (not_iff_elim (ne_symm pred))) ◂ Heq,
                      ex_some  : ∃ b, proj2 (rep n) = some b          := resolve1 (optional::dichotomy (proj2 (rep n))) neq_none
                  in obtain (b : B) (Hb : proj2 (rep n) = some b), from ex_some,
                     or_intror (∃ a, n = inl a B)
                               (let rep_eq   : rep n         = pair none (some b)
                                             := pairext_proj Heq Hb,
                                    rep_inr  : rep (inr A b) = pair none (some b)
                                             := rep_abst (inhabr A (inhabited_intro b)) (pair none (some b)) (inr_pred A b),
                                    n_eq_inr : n = inr A b
                                             := rep_inj (trans rep_eq (symm rep_inr))
                                in exists_intro b n_eq_inr))
         (λ Hne, let eq_none : proj2 (rep n) = (optional::@none B) := (not_iff_elim pred) ◂ Hne,
                     ex_some : ∃ a, proj1 (rep n) = some a := resolve1 (optional::dichotomy (proj1 (rep n))) Hne
                 in obtain (a : A) (Ha : proj1 (rep n) = some a), from ex_some,
                    or_introl (let rep_eq   : rep n  = pair (some a) none
                                            := pairext_proj Ha eq_none,
                                   rep_inl  : rep (inl a B) = pair (some a) none
                                            := rep_abst (inhabl (inhabited_intro a) B) (pair (some a) none) (inl_pred a B),
                                   n_eq_inl : n = inl a B
                                            := rep_inj (trans rep_eq (symm rep_inl))
                               in exists_intro a n_eq_inl)
                              (∃ b, n = inr A b))

theorem induction {A B : (Type U)} {P : sum A B → Bool} (H1 : ∀ a, P (inl a B)) (H2 : ∀ b, P (inr A b)) : ∀ n, P n
:= take n, or_elim (sum::dichotomy n)
    (λ Hex : ∃ a, n = inl a B,
        obtain (a : A) (Ha : n = inl a B), from Hex,
          subst (H1 a) (symm Ha))
    (λ Hex : ∃ b, n = inr A b,
        obtain (b : B) (Hb : n = inr A b), from Hex,
           subst (H2 b) (symm Hb))

set_opaque inl true
set_opaque inr true
end
set_opaque sum_pred true
set_opaque sum      true
