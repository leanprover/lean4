-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic

axiom boolcomplete (a : Bool) : a = true ∨ a = false

theorem case (P : Bool → Bool) (H1 : P true) (H2 : P false) (a : Bool) : P a
:= or_elim (boolcomplete a)
     (assume Ht : a = true,  subst (symm Ht) H1)
     (assume Hf : a = false, subst (symm Hf) H2)

theorem em (a : Bool) : a ∨ ¬ a
:= or_elim (boolcomplete a)
     (assume Ht : a = true,  or_intro_left (¬ a) (eqt_elim Ht))
     (assume Hf : a = false, or_intro_right a (eqf_elim Hf))

theorem boolcomplete_swapped (a : Bool) : a = false ∨ a = true
:= case (λ x, x = false ∨ x = true)
        (or_intro_right (true = false) (refl true))
        (or_intro_left  (false = true) (refl false))
        a

theorem not_true : (¬ true) = false
:= have aux : ¬ (¬ true) = true, from
     not_intro (assume H : (¬ true) = true,
       absurd_not_true (subst (symm H) trivial)),
   resolve_right (boolcomplete (¬ true)) aux

theorem not_false : (¬ false) = true
:= have aux : ¬ (¬ false) = false, from
     not_intro (assume H : (¬ false) = false,
        subst H not_false_trivial),
   resolve_right (boolcomplete_swapped (¬ false)) aux

theorem not_not_eq (a : Bool) : (¬ ¬ a) = a
:= case (λ x, (¬ ¬ x) = x)
        (calc (¬ ¬ true)  = (¬ false) : { not_true }
                    ...   = true      : not_false)
        (calc (¬ ¬ false) = (¬ true)  : { not_false }
                    ...   = false     : not_true)
        a

theorem not_not_elim {a : Bool} (H : ¬ ¬ a) : a
:= (not_not_eq a) ◂ H

theorem boolext {a b : Bool} (Hab : a → b) (Hba : b → a) : a = b
:= or_elim (boolcomplete a)
       (λ Hat : a = true,  or_elim (boolcomplete b)
           (λ Hbt : b = true,  trans Hat (symm Hbt))
           (λ Hbf : b = false, false_elim (a = b) (subst Hbf (Hab (eqt_elim Hat)))))
       (λ Haf : a = false, or_elim (boolcomplete b)
           (λ Hbt : b = true,  false_elim (a = b) (subst Haf (Hba (eqt_elim Hbt))))
           (λ Hbf : b = false, trans Haf (symm Hbf)))

theorem iff_to_eq {a b : Bool} (H : a ↔ b) : a = b
:= iff_elim (assume H1 H2, boolext H1 H2) H

theorem iff_eq_eq {a b : Bool} : (a ↔ b) = (a = b)
:= boolext
     (assume H, iff_to_eq H)
     (assume H, eq_to_iff H)

theorem eqt_intro {a : Bool} (H : a) : a = true
:= boolext (assume H1 : a,    trivial)
           (assume H2 : true, H)

theorem eqf_intro {a : Bool} (H : ¬ a) : a = false
:= boolext (assume H1 : a,     absurd H1 H)
           (assume H2 : false, false_elim a H2)

theorem by_contradiction {a : Bool} (H : ¬ a → false) : a
:= or_elim (em a) (λ H1 : a, H1) (λ H1 : ¬ a, false_elim a (H H1))

theorem a_neq_a {A : Type} (a : A) : (a ≠ a) = false
:= boolext (assume H, a_neq_a_elim H)
           (assume H, false_elim (a ≠ a) H)

theorem eq_id {A : Type} (a : A) : (a = a) = true
:= eqt_intro (refl a)

theorem heq_id {A : Type} (a : A) : (a == a) = true
:= eqt_intro (hrefl a)

theorem not_or (a b : Bool) : (¬ (a ∨ b)) = (¬ a ∧ ¬ b)
:= boolext
     (assume H, or_elim (em a)
       (assume Ha, absurd_elim (¬ a ∧ ¬ b) (or_intro_left b Ha) H)
       (assume Hna, or_elim (em b)
         (assume Hb, absurd_elim (¬ a ∧ ¬ b) (or_intro_right a Hb) H)
         (assume Hnb, and_intro Hna Hnb)))
     (assume (H : ¬ a ∧ ¬ b), not_intro (assume (N : a ∨ b),
       or_elim N
         (assume Ha, absurd Ha (and_elim_left H))
         (assume Hb, absurd Hb (and_elim_right H))))

theorem not_and (a b : Bool) : (¬ (a ∧ b)) = (¬ a ∨ ¬ b)
:= boolext
     (assume H, or_elim (em a)
       (assume Ha, or_elim (em b)
       (assume Hb, absurd_elim (¬ a ∨ ¬ b) (and_intro Ha Hb) H)
         (assume Hnb, or_intro_right (¬ a) Hnb))
         (assume Hna, or_intro_left (¬ b) Hna))
     (assume (H : ¬ a ∨ ¬ b), not_intro (assume (N : a ∧ b),
       or_elim H
         (assume Hna, absurd (and_elim_left N) Hna)
         (assume Hnb, absurd (and_elim_right N) Hnb)))

theorem imp_or (a b : Bool) : (a → b) = (¬ a ∨ b)
:= boolext
     (assume H : a → b,
        (or_elim (em a)
           (λ Ha  : a,   or_intro_right (¬ a) (H Ha))
           (λ Hna : ¬ a, or_intro_left b Hna)))
     (assume H : ¬ a ∨ b,
        assume Ha : a,
          resolve_right H ((symm (not_not_eq a)) ◂ Ha))

theorem not_implies (a b : Bool) : (¬ (a → b)) = (a ∧ ¬ b)
:= calc (¬ (a → b)) = (¬ (¬ a ∨ b))  : {imp_or a b}
                 ... = (¬ ¬ a ∧ ¬ b)  : not_or (¬ a) b
                 ... = (a ∧ ¬ b)      : {not_not_eq a}

theorem a_eq_not_a (a : Bool) : (a = ¬ a) = false
:= boolext
     (assume H, or_elim (em a)
       (assume Ha, absurd Ha (subst H Ha))
       (assume Hna, absurd (subst (symm H) Hna) Hna))
     (assume H, false_elim (a = ¬ a) H)

theorem true_eq_false : (true = false) = false
:= subst not_true (a_eq_not_a true)

theorem false_eq_true : (false = true) = false
:= subst not_false (a_eq_not_a false)

theorem a_eq_true (a : Bool) : (a = true) = a
:= boolext
     (assume H, eqt_elim H)
     (assume H, eqt_intro H)

theorem a_eq_false (a : Bool) : (a = false) = (¬ a)
:= boolext
     (assume H, eqf_elim H)
     (assume H, eqf_intro H)
