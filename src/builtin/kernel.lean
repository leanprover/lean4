-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import macros
import tactic

universe U ≥ 1
definition TypeU := (Type U)

-- create default rewrite rule set
(* mk_rewrite_rule_set() *)

variable Bool : Type

-- Reflexivity for heterogeneous equality
-- We use universe U+1 in heterogeneous equality axioms because we want to be able
-- to state the equality between A and B of (Type U)
axiom hrefl {A : (Type U+1)} (a : A) : a == a

-- Homogeneous equality
definition eq {A : (Type U)} (a b : A) := a == b
infix 50 = : eq

theorem refl {A : (Type U)} (a : A) : a = a
:= hrefl a

theorem heq_eq {A : (Type U)} (a b : A) : (a == b) = (a = b)
:= refl (a == b)

definition true : Bool
:= (λ x : Bool, x) = (λ x : Bool, x)

theorem trivial : true
:= refl (λ x : Bool, x)

set_opaque true true

definition false : Bool
:= ∀ x : Bool, x

set_opaque false true
alias ⊤ : true
alias ⊥ : false

definition not (a : Bool) := a → false
notation 40 ¬ _ : not

definition or (a b : Bool) := ¬ a → b
infixr 30 || : or
infixr 30 \/ : or
infixr 30 ∨  : or

definition and (a b : Bool) := ¬ (a → ¬ b)
infixr 35 && : and
infixr 35 /\ : and
infixr 35 ∧  : and

definition implies (a b : Bool) := a → b

definition neq {A : (Type U)} (a b : A) := ¬ (a = b)
infix 50 ≠ : neq

theorem a_neq_a_elim {A : (Type U)} {a : A} (H : a ≠ a) : false
:= H (refl a)

definition iff (a b : Bool) := a = b
infixr 25 <-> : iff
infixr 25 ↔   : iff

theorem em (a : Bool) : a ∨ ¬ a
:= assume Hna : ¬ a, Hna

theorem not_intro {a : Bool} (H : a → false) : ¬ a
:= H

theorem absurd {a : Bool} (H1 : a) (H2 : ¬ a) : false
:= H2 H1

-- The Lean parser has special treatment for the constant exists.
-- It allows us to write
--      exists x y : A, P x y   and    ∃ x y : A, P x y
-- as syntax sugar for
--      exists A (fun x : A, exists A (fun y : A, P x y))
-- That is, it treats the exists as an extra binder such as fun and forall.
-- It also provides an alias (Exists) that should be used when we
-- want to treat exists as a constant.
definition Exists (A : (Type U)) (P : A → Bool)
:= ¬ (∀ x, ¬ (P x))

definition exists_unique {A : (Type U)} (p : A → Bool)
:= ∃ x, p x ∧ ∀ y, y ≠ x → ¬ p y

axiom case (P : Bool → Bool) (H1 : P true) (H2 : P false) (a : Bool) : P a

theorem false_elim (a : Bool) (H : false) : a
:= case (λ x, x) trivial H a

theorem mt {a b : Bool} (H1 : a → b) (H2 : ¬ b) : ¬ a
:= assume Ha : a, absurd (H1 Ha) H2

theorem contrapos {a b : Bool} (H : a → b) : ¬ b → ¬ a
:= assume Hnb : ¬ b, mt H Hnb

theorem absurd_elim {a : Bool} (b : Bool) (H1 : a) (H2 : ¬ a) : b
:= false_elim b (absurd H1 H2)

-- Recall that or is defined as ¬ a → b
theorem or_introl {a : Bool} (H : a) (b : Bool) : a ∨ b
:= assume H1 : ¬ a, absurd_elim b H H1

theorem or_intror {b : Bool} (a : Bool) (H : b) : a ∨ b
:= assume H1 : ¬ a, H

theorem boolcomplete (a : Bool) : a = true ∨ a = false
:= case (λ x, x = true ∨ x = false)
        (or_introl (refl true) (true = false))
        (or_intror (false = true) (refl false))
        a

theorem boolcomplete_swapped (a : Bool) : a = false ∨ a = true
:= case (λ x, x = false ∨ x = true)
        (or_intror (true = false) (refl true))
        (or_introl (refl false) (false = true))
        a

theorem resolve1 {a b : Bool} (H1 : a ∨ b) (H2 : ¬ a) : b
:= H1 H2

axiom subst {A : (Type U)} {a b : A} {P : A → Bool} (H1 : P a) (H2 : a = b) : P b

-- Alias for subst where we provide P explicitly, but keep A,a,b implicit
theorem substp {A : (Type U)} {a b : A} (P : A → Bool) (H1 : P a) (H2 : a = b) : P b
:= subst H1 H2

theorem symm {A : (Type U)} {a b : A} (H : a = b) : b = a
:= subst (refl a) H

theorem trans {A : (Type U)} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c
:= subst H1 H2

theorem congr1 {A B : (Type U)} {f g : A → B} (a : A) (H : f = g) : f a = g a
:= substp (fun h : A → B, f a = h a) (refl (f a)) H

theorem congr2 {A B : (Type U)} {a b : A} (f : A → B) (H : a = b) : f a = f b
:= substp (fun x : A, f a = f x) (refl (f a)) H

theorem congr {A B : (Type U)} {f g : A → B} {a b : A} (H1 : f = g) (H2 : a = b) : f a = g b
:= subst (congr2 f H2) (congr1 b H1)

theorem true_ne_false : ¬ true = false
:= assume H : true = false,
     subst trivial H

theorem absurd_not_true (H : ¬ true) : false
:= absurd trivial H

theorem not_false_trivial : ¬ false
:= assume H : false, H

-- "equality modus pones"
theorem eqmp {a b : Bool} (H1 : a = b) (H2 : a) : b
:= subst H2 H1

infixl 100 <| : eqmp
infixl 100 ◂  : eqmp

theorem eqmpr {a b : Bool} (H1 : a = b) (H2 : b) : a
:= (symm H1) ◂ H2

theorem imp_trans {a b c : Bool} (H1 : a → b) (H2 : b → c) : a → c
:= assume Ha, H2 (H1 Ha)

theorem imp_eq_trans {a b c : Bool} (H1 : a → b) (H2 : b = c) : a → c
:= assume Ha, H2 ◂ (H1 Ha)

theorem eq_imp_trans {a b c : Bool} (H1 : a = b) (H2 : b → c) : a → c
:= assume Ha, H2 (H1 ◂ Ha)

theorem to_eq {A : (Type U)} {a b : A} (H : a == b) : a = b
:= (heq_eq a b) ◂ H

theorem to_heq {A : (Type U)} {a b : A} (H : a = b) : a == b
:= (symm (heq_eq a b)) ◂ H

theorem iff_eliml {a b : Bool} (H : a ↔ b) : a → b
:= (λ Ha : a, eqmp H Ha)

theorem iff_elimr {a b : Bool} (H : a ↔ b) : b → a
:= (λ Hb : b, eqmpr H Hb)

theorem ne_symm {A : (Type U)} {a b : A} (H : a ≠ b) : b ≠ a
:= assume H1 : b = a, H (symm H1)

theorem eq_ne_trans {A : (Type U)} {a b c : A} (H1 : a = b) (H2 : b ≠ c) : a ≠ c
:= subst H2 (symm H1)

theorem ne_eq_trans {A : (Type U)} {a b c : A} (H1 : a ≠ b) (H2 : b = c) : a ≠ c
:= subst H1 H2

theorem eqt_elim {a : Bool} (H : a = true) : a
:= (symm H) ◂ trivial

theorem eqf_elim {a : Bool} (H : a = false) : ¬ a
:= not_intro (λ Ha : a, H ◂ Ha)

theorem heqt_elim {a : Bool} (H : a == true) : a
:= eqt_elim (to_eq H)

theorem not_true : (¬ true) = false
:= let aux : ¬ (¬ true) = true
           := assume H : (¬ true) = true,
                absurd_not_true (subst trivial (symm H))
   in resolve1 (boolcomplete (¬ true)) aux

theorem not_false : (¬ false) = true
:= let aux : ¬ (¬ false) = false
           := assume H : (¬ false) = false,
                subst not_false_trivial H
   in resolve1 (boolcomplete_swapped (¬ false)) aux

add_rewrite not_true not_false

theorem not_not_eq (a : Bool) : (¬ ¬ a) = a
:= case (λ x, (¬ ¬ x) = x)
        (calc (¬ ¬ true)  = (¬ false) : { not_true }
                    ...   = true      : not_false)
        (calc (¬ ¬ false) = (¬ true)  : { not_false }
                    ...   = false     : not_true)
        a

add_rewrite not_not_eq

theorem not_neq {A : (Type U)} (a b : A) : ¬ (a ≠ b) ↔ a = b
:= not_not_eq (a = b)

add_rewrite not_neq

theorem not_neq_elim {A : (Type U)} {a b : A} (H : ¬ (a ≠ b)) : a = b
:= (not_neq a b) ◂ H

theorem not_not_elim {a : Bool} (H : ¬ ¬ a) : a
:= (not_not_eq a) ◂ H

theorem not_imp_eliml {a b : Bool} (Hnab : ¬ (a → b)) : a
:= not_not_elim
      (show ¬ ¬ a,
       from assume Hna : ¬ a, absurd (assume Ha : a, absurd_elim b Ha Hna)
                                      Hnab)

theorem not_imp_elimr {a b : Bool} (H : ¬ (a → b)) : ¬ b
:= assume Hb : b, absurd (assume Ha : a, Hb)
                         H

-- Recall that and is defined as ¬ (a → ¬ b)
theorem and_intro {a b : Bool} (H1 : a) (H2 : b) : a ∧ b
:= assume H : a → ¬ b, absurd H2 (H H1)

theorem and_eliml {a b : Bool} (H : a ∧ b) : a
:= not_imp_eliml H

theorem and_elimr {a b : Bool} (H : a ∧ b) : b
:= not_not_elim (not_imp_elimr H)

theorem or_elim {a b c : Bool} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
:= not_not_elim
     (assume H : ¬ c,
        absurd (H3 (resolve1 H1 (mt (assume Ha : a, H2 Ha) H)))
               H)

theorem refute {a : Bool} (H : ¬ a → false) : a
:= or_elim (em a) (λ H1 : a, H1) (λ H1 : ¬ a, false_elim a (H H1))

theorem boolext {a b : Bool} (Hab : a → b) (Hba : b → a) : a = b
:= or_elim (boolcomplete a)
       (λ Hat : a = true,  or_elim (boolcomplete b)
           (λ Hbt : b = true,  trans Hat (symm Hbt))
           (λ Hbf : b = false, false_elim (a = b) (subst (Hab (eqt_elim Hat)) Hbf)))
       (λ Haf : a = false, or_elim (boolcomplete b)
           (λ Hbt : b = true,  false_elim (a = b) (subst (Hba (eqt_elim Hbt)) Haf))
           (λ Hbf : b = false, trans Haf (symm Hbf)))

-- Another name for boolext
theorem iff_intro {a b : Bool} (Hab : a → b) (Hba : b → a) : a ↔ b
:= boolext Hab Hba

theorem eqt_intro {a : Bool} (H : a) : a = true
:= boolext (assume H1 : a,    trivial)
           (assume H2 : true, H)

theorem eqf_intro {a : Bool} (H : ¬ a) : a = false
:= boolext (assume H1 : a,     absurd H1 H)
           (assume H2 : false, false_elim a H2)

theorem a_neq_a {A : (Type U)} (a : A) : (a ≠ a) ↔ false
:= boolext (assume H, a_neq_a_elim H)
           (assume H, false_elim (a ≠ a) H)

theorem eq_id {A : (Type U)} (a : A) : (a = a) ↔ true
:= eqt_intro (refl a)

theorem iff_id (a : Bool) : (a ↔ a) ↔ true
:= eqt_intro (refl a)

theorem heq_id (A : (Type U+1)) (a : A) : (a == a) ↔ true
:= eqt_intro (hrefl a)

theorem neq_elim {A : (Type U)} {a b : A} (H : a ≠ b) : a = b ↔ false
:= eqf_intro H

theorem neq_to_not_eq {A : (Type U)} {a b : A} : a ≠ b ↔ ¬ a = b
:= refl (a ≠ b)

add_rewrite eq_id iff_id neq_to_not_eq

-- Remark: ordered rewriting + assoc + comm + left_comm sorts a term lexicographically
theorem left_comm {A : (Type U)} {R : A -> A -> A} (comm : ∀ x y, R x y = R y x) (assoc : ∀ x y z, R (R x y) z = R x (R y z)) :
        ∀ x y z, R x (R y z) = R y (R x z)
:= take x y z, calc R x (R y z) = R (R x y) z : symm (assoc x y z)
                         ...    = R (R y x) z : { comm x y }
                         ...    = R y (R x z) : assoc y x z

theorem or_comm (a b : Bool) : (a ∨ b) = (b ∨ a)
:= boolext (assume H, or_elim H (λ H1, or_intror b H1) (λ H2, or_introl H2 a))
           (assume H, or_elim H (λ H1, or_intror a H1) (λ H2, or_introl H2 b))

theorem or_assoc (a b c : Bool) : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c)
:= boolext (assume H : (a ∨ b) ∨ c,
                      or_elim H (λ H1 : a ∨ b, or_elim H1 (λ Ha : a, or_introl Ha (b ∨ c))
                                                          (λ Hb : b, or_intror a (or_introl Hb c)))
                                (λ Hc : c, or_intror a (or_intror b Hc)))
           (assume H : a ∨ (b ∨ c),
                      or_elim H (λ Ha : a, (or_introl (or_introl Ha b) c))
                                (λ H1 : b ∨ c, or_elim H1 (λ Hb : b, or_introl (or_intror a Hb) c)
                                                          (λ Hc : c, or_intror (a ∨ b) Hc)))

theorem or_id (a : Bool) : a ∨ a ↔ a
:= boolext (assume H, or_elim H (λ H1, H1) (λ H2, H2))
           (assume H, or_introl H a)

theorem or_falsel (a : Bool) : a ∨ false ↔ a
:= boolext (assume H, or_elim H (λ H1, H1) (λ H2, false_elim a H2))
           (assume H, or_introl H false)

theorem or_falser (a : Bool) : false ∨ a ↔ a
:= trans (or_comm false a) (or_falsel a)

theorem or_truel (a : Bool) : true ∨ a ↔ true
:= boolext (assume H : true ∨ a, trivial)
           (assume H : true, or_introl trivial a)

theorem or_truer (a : Bool) : a ∨ true ↔ true
:= trans (or_comm a true) (or_truel a)

theorem or_tauto (a : Bool) : a ∨ ¬ a ↔ true
:= eqt_intro (em a)

theorem or_left_comm (a b c : Bool) : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c)
:= left_comm or_comm or_assoc a b c

add_rewrite or_comm or_assoc or_id or_falsel or_falser or_truel or_truer or_tauto or_left_comm

theorem resolve2 {a b : Bool} (H1 : a ∨ b) (H2 : ¬ b) : a
:= resolve1 ((or_comm a b) ◂ H1) H2

theorem and_comm (a b : Bool) : a ∧ b ↔ b ∧ a
:= boolext (assume H, and_intro (and_elimr H) (and_eliml H))
           (assume H, and_intro (and_elimr H) (and_eliml H))

theorem and_id (a : Bool) : a ∧ a ↔ a
:= boolext (assume H, and_eliml H)
           (assume H, and_intro H H)

theorem and_assoc (a b c : Bool) : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c)
:= boolext (assume H, and_intro (and_eliml (and_eliml H)) (and_intro (and_elimr (and_eliml H)) (and_elimr H)))
           (assume H, and_intro (and_intro (and_eliml H) (and_eliml (and_elimr H))) (and_elimr (and_elimr H)))

theorem and_truer (a : Bool) : a ∧ true ↔ a
:= boolext (assume H : a ∧ true,  and_eliml H)
           (assume H : a,         and_intro H trivial)

theorem and_truel (a : Bool) : true ∧ a ↔ a
:= trans (and_comm true a) (and_truer a)

theorem and_falsel (a : Bool) : a ∧ false ↔ false
:= boolext (assume H, and_elimr H)
           (assume H, false_elim (a ∧ false) H)

theorem and_falser (a : Bool) : false ∧ a ↔ false
:= trans (and_comm false a) (and_falsel a)

theorem and_absurd (a : Bool) : a ∧ ¬ a ↔ false
:= boolext (assume H, absurd (and_eliml H) (and_elimr H))
           (assume H, false_elim (a ∧ ¬ a) H)

theorem and_left_comm (a b c : Bool) : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c)
:= left_comm and_comm and_assoc a b c

add_rewrite and_comm and_assoc and_id and_falsel and_falser and_truel and_truer and_absurd and_left_comm

theorem imp_truer (a : Bool) : (a → true) ↔ true
:= boolext (assume H, trivial)
           (assume H Ha, trivial)

theorem imp_truel (a : Bool) : (true → a) ↔ a
:= boolext (assume H : true → a, H trivial)
           (assume Ha H, Ha)

theorem imp_falser (a : Bool) : (a → false) ↔ ¬ a
:= refl _

theorem imp_falsel (a : Bool) : (false → a) ↔ true
:= boolext (assume H, trivial)
           (assume H Hf, false_elim a Hf)

theorem imp_id (a : Bool) : (a → a) ↔ true
:= eqt_intro (λ H : a, H)

add_rewrite imp_truer imp_truel imp_falser imp_falsel imp_id

theorem imp_or (a b : Bool) : (a → b) ↔ ¬ a ∨ b
:= boolext
     (assume H : a → b,
        (or_elim (em a)
           (λ Ha  : a,   or_intror (¬ a) (H Ha))
           (λ Hna : ¬ a, or_introl Hna b)))
     (assume H : ¬ a ∨ b,
        assume Ha : a,
          resolve1 H ((symm (not_not_eq a)) ◂ Ha))

theorem not_congr {a b : Bool} (H : a ↔ b) : ¬ a ↔ ¬ b
:= congr2 not H

-- Recall that exists is defined as ¬ ∀ x : A, ¬ P x
theorem exists_elim {A : (Type U)} {P : A → Bool} {B : Bool} (H1 : Exists A P) (H2 : ∀ (a : A) (H : P a), B) : B
:= refute (λ R : ¬ B,
             absurd (take a : A, mt (assume H : P a, H2 a H) R)
                    H1)

theorem exists_intro {A : (Type U)} {P : A → Bool} (a : A) (H : P a) : Exists A P
:= assume H1 : (∀ x : A, ¬ P x),
      absurd H (H1 a)

theorem not_exists (A : (Type U)) (P : A → Bool) : ¬ (∃ x : A, P x) ↔ (∀ x : A, ¬ P x)
:= calc (¬ ∃ x : A, P x) = ¬ ¬ ∀ x : A, ¬ P x : refl (¬ ∃ x : A, P x)
                     ... = ∀ x : A, ¬ P x     : not_not_eq (∀ x : A, ¬ P x)

theorem not_exists_elim {A : (Type U)} {P : A → Bool} (H : ¬ ∃ x : A, P x) : ∀ x : A, ¬ P x
:= (not_exists A P) ◂ H

theorem exists_unfold1 {A : (Type U)} {P : A → Bool} (a : A) (H : ∃ x : A, P x) : P a ∨ (∃ x : A, x ≠ a ∧ P x)
:= exists_elim H
     (λ (w : A) (H1 : P w),
        or_elim (em (w = a))
          (λ Heq : w = a, or_introl (subst H1 Heq) (∃ x : A, x ≠ a ∧ P x))
          (λ Hne : w ≠ a, or_intror (P a) (exists_intro w (and_intro Hne H1))))

theorem exists_unfold2 {A : (Type U)} {P : A → Bool} (a : A) (H : P a ∨ (∃ x : A, x ≠ a ∧ P x)) : ∃ x : A, P x
:= or_elim H
      (λ H1 : P a, exists_intro a H1)
      (λ H2 : (∃ x : A, x ≠ a ∧ P x),
          exists_elim H2
               (λ (w : A) (Hw : w ≠ a ∧ P w),
                  exists_intro w (and_elimr Hw)))

theorem exists_unfold {A : (Type U)} (P : A → Bool) (a : A) : (∃ x : A, P x) ↔ (P a ∨ (∃ x : A, x ≠ a ∧ P x))
:= boolext (assume H : (∃ x : A, P x),                 exists_unfold1 a H)
           (assume H : (P a ∨ (∃ x : A, x ≠ a ∧ P x)), exists_unfold2 a H)

definition inhabited (A : (Type U))
:= ∃ x : A, true

-- If we have an element of type A, then A is inhabited
theorem inhabited_intro {A : (Type U)} (a : A) : inhabited A
:= assume H : (∀ x, ¬ true), absurd_not_true (H a)

theorem inhabited_elim {A : (Type U)} (H1 : inhabited A) {B : Bool} (H2 : A → B) : B
:= obtain (w : A) (Hw : true), from H1,
     H2 w

theorem inhabited_ex_intro {A : (Type U)} {P : A → Bool} (H : ∃ x, P x) : inhabited A
:= obtain (w : A) (Hw : P w), from H,
      exists_intro w trivial

-- If a function space is non-empty, then for every 'a' in the domain, the range (B a) is not empty
theorem inhabited_range {A : (Type U)} {B : A → (Type U)} (H : inhabited (∀ x, B x)) (a : A) : inhabited (B a)
:= refute (λ N : ¬ inhabited (B a),
     let s1 : ¬ ∃ x : B a, true       := N,
         s2 : ∀ x : B a, false        := take x : B a, absurd_not_true (not_exists_elim s1 x),
         s3 : ∃ y : (∀ x, B x), true := H
     in obtain (w : (∀ x, B x)) (Hw : true), from s3,
           let s4 : B a := w a
           in s2 s4)

theorem exists_rem {A : (Type U)} (H : inhabited A) (p : Bool) : (∃ x : A, p) ↔ p
:= iff_intro
    (assume Hl : (∃ x : A, p),
       obtain (w : A) (Hw : p), from Hl,
         Hw)
    (assume Hr : p,
       inhabited_elim H (λ w, exists_intro w Hr))

theorem forall_rem {A : (Type U)} (H : inhabited A) (p : Bool) : (∀ x : A, p) ↔ p
:= iff_intro
    (assume Hl : (∀ x : A, p),
       inhabited_elim H (λ w, Hl w))
    (assume Hr : p,
       take x, Hr)

-- Congruence theorems for contextual simplification

-- Simplify a → b, by first simplifying a to c using the fact that ¬ b is true, and then
-- b to d using the fact that c is true
theorem imp_congrr {a b c d : Bool} (H_ac : ∀ (H_nb : ¬ b), a = c) (H_bd : ∀ (H_c : c), b = d) : (a → b) = (c → d)
:= or_elim (em b)
      (λ H_b : b,
          or_elim (em c)
             (λ H_c : c,
                   calc (a → b) =  (a → true)  : { eqt_intro H_b }
                            ...  = true          : imp_truer a
                            ...  = (c → true)  :  symm (imp_truer c)
                            ...  = (c → b)     : { symm (eqt_intro H_b) }
                            ...  = (c → d)     : { H_bd H_c })
             (λ H_nc : ¬ c,
                 calc (a → b) = (a → true)   : { eqt_intro H_b }
                          ...  = true          : imp_truer a
                          ...  = (false → d)  : symm (imp_falsel d)
                          ...  = (c → d)      : { symm (eqf_intro H_nc) }))
      (λ H_nb : ¬ b,
          or_elim (em c)
             (λ H_c : c,
                 calc (a → b) = (c → b)  : { H_ac H_nb }
                          ...  = (c → d)  : { H_bd H_c })
             (λ H_nc : ¬ c,
                 calc (a → b) = (c → b) : { H_ac H_nb }
                          ...  = (false → b) : { eqf_intro H_nc }
                          ...  = true         : imp_falsel b
                          ...  = (false → d) : symm (imp_falsel d)
                          ...  = (c → d)  :  { symm (eqf_intro H_nc) }))


-- Simplify a → b, by first simplifying b to d using the fact that a is true, and then
-- b to d using the fact that ¬ d is true.
-- This kind of congruence seems to be useful in very rare cases.
theorem imp_congrl {a b c d : Bool} (H_bd : ∀ (H_a : a), b = d) (H_ac : ∀ (H_nd : ¬ d), a = c) : (a → b) = (c → d)
:= or_elim (em a)
      (λ H_a : a,
          or_elim (em d)
             (λ H_d : d,
                 calc (a → b) = (a → d)    : { H_bd H_a }
                          ...  = (a → true) : { eqt_intro H_d }
                          ...  = true         :  imp_truer a
                          ...  = (c → true)  : symm (imp_truer c)
                          ...  = (c → d)     : { symm (eqt_intro H_d) })
             (λ H_nd : ¬ d,
                 calc (a → b) = (c → b)   : { H_ac H_nd }
                          ...  = (c → d)   : { H_bd H_a }))
      (λ H_na : ¬ a,
          or_elim (em d)
             (λ H_d : d,
                 calc (a → b) = (false → b)   :  { eqf_intro H_na }
                          ...  = true           : imp_falsel b
                          ...  = (c → true)    : symm (imp_truer c)
                          ...  = (c → d)       : { symm (eqt_intro H_d) })
             (λ H_nd : ¬ d,
                 calc (a → b) = (false → b) : { eqf_intro H_na }
                          ...  = true         : imp_falsel b
                          ...  = (false → d) : symm (imp_falsel d)
                          ...  = (a → d)  :  { symm (eqf_intro H_na) }
                          ...  = (c → d)  :  { H_ac H_nd }))

-- (Common case) simplify a to c, and then b to d using the fact that c is true
theorem imp_congr {a b c d : Bool} (H_ac : a = c) (H_bd : ∀ (H_c : c), b = d) : (a → b) = (c → d)
:= imp_congrr (λ H, H_ac) H_bd

-- In the following theorems we are using the fact that a ∨ b is defined as ¬ a → b
theorem or_congrr {a b c d : Bool} (H_ac : ∀ (H_nb : ¬ b), a = c) (H_bd : ∀ (H_nc : ¬ c), b = d) : a ∨ b ↔ c ∨ d
:= imp_congrr (λ H_nb : ¬ b, congr2 not (H_ac H_nb)) H_bd
theorem or_congrl {a b c d : Bool} (H_bd : ∀ (H_na : ¬ a), b = d) (H_ac : ∀ (H_nd : ¬ d), a = c) : a ∨ b ↔ c ∨ d
:= imp_congrl H_bd (λ H_nd : ¬ d, congr2 not (H_ac H_nd))
-- (Common case) simplify a to c, and then b to d using the fact that ¬ c is true
theorem or_congr {a b c d : Bool} (H_ac : a = c) (H_bd : ∀ (H_nc : ¬ c), b = d) : a ∨ b ↔ c ∨ d
:= or_congrr (λ H, H_ac) H_bd

-- In the following theorems we are using the fact hat a ∧ b is defined as ¬ (a → ¬ b)
theorem and_congrr {a b c d : Bool} (H_ac : ∀ (H_b : b), a = c) (H_bd : ∀ (H_c : c), b = d) : a ∧ b ↔ c ∧ d
:= congr2 not (imp_congrr (λ (H_nnb : ¬ ¬ b), H_ac (not_not_elim H_nnb)) (λ H_c : c, congr2 not (H_bd H_c)))
theorem and_congrl {a b c d : Bool} (H_bd : ∀ (H_a : a), b = d) (H_ac : ∀ (H_d : d), a = c) : a ∧ b ↔ c ∧ d
:= congr2 not (imp_congrl (λ H_a : a, congr2 not (H_bd H_a)) (λ (H_nnd : ¬ ¬ d), H_ac (not_not_elim H_nnd)))
-- (Common case) simplify a to c, and then b to d using the fact that c is true
theorem and_congr {a b c d : Bool} (H_ac : a = c) (H_bd : ∀ (H_c : c), b = d) : a ∧ b ↔ c ∧ d
:= and_congrr (λ H, H_ac) H_bd

theorem not_and (a b : Bool) : ¬ (a ∧ b) ↔ ¬ a ∨ ¬ b
:= boolext (assume H, or_elim (em a)
               (assume Ha, or_elim (em b)
                     (assume Hb, absurd_elim (¬ a ∨ ¬ b) (and_intro Ha Hb) H)
                     (assume Hnb, or_intror (¬ a) Hnb))
               (assume Hna, or_introl Hna (¬ b)))
           (assume (H : ¬ a ∨ ¬ b) (N : a ∧ b),
               or_elim H
                 (assume Hna, absurd (and_eliml N) Hna)
                 (assume Hnb, absurd (and_elimr N) Hnb))

theorem not_and_elim {a b : Bool} (H : ¬ (a ∧ b)) : ¬ a ∨ ¬ b
:= (not_and a b) ◂ H

theorem not_or (a b : Bool) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b
:= boolext (assume H, or_elim (em a)
               (assume Ha, absurd_elim (¬ a ∧ ¬ b) (or_introl Ha b) H)
               (assume Hna, or_elim (em b)
                   (assume Hb, absurd_elim (¬ a ∧ ¬ b) (or_intror a Hb) H)
                   (assume Hnb, and_intro Hna Hnb)))
           (assume (H : ¬ a ∧ ¬ b) (N : a ∨ b),
               or_elim N
                 (assume Ha, absurd Ha (and_eliml H))
                 (assume Hb, absurd Hb (and_elimr H)))

theorem not_or_elim {a b : Bool} (H : ¬ (a ∨ b)) : ¬ a ∧ ¬ b
:= (not_or a b) ◂ H

theorem not_implies (a b : Bool) : ¬ (a → b) ↔ a ∧ ¬ b
:= calc (¬ (a → b)) = ¬ (¬ a ∨ b)  : { imp_or a b }
                 ... = ¬ ¬ a ∧ ¬ b  : not_or (¬ a) b
                 ... = a ∧ ¬ b      : by simp

theorem not_implies_elim {a b : Bool} (H : ¬ (a → b)) : a ∧ ¬ b
:= (not_implies a b) ◂ H

theorem a_eq_not_a (a : Bool) : (a = ¬ a) ↔ false
:= boolext (λ H, or_elim (em a)
                 (λ Ha, absurd Ha (subst Ha H))
                 (λ Hna, absurd (subst Hna (symm H)) Hna))
           (λ H, false_elim (a = ¬ a) H)

theorem a_iff_not_a (a : Bool) : (a ↔ ¬ a) ↔ false
:= a_eq_not_a a

theorem true_eq_false : (true = false) ↔ false
:= subst (a_eq_not_a true) not_true

theorem true_iff_false : (true ↔ false) ↔ false
:= true_eq_false

theorem false_eq_true : (false = true) ↔ false
:= subst (a_eq_not_a false) not_false

theorem false_iff_true : (false ↔ true) ↔ false
:= false_eq_true

theorem a_iff_true (a : Bool) : (a ↔ true) ↔ a
:= boolext (λ H, eqt_elim H)
           (λ H, eqt_intro H)

theorem a_iff_false (a : Bool) : (a ↔ false) ↔ ¬ a
:= boolext (λ H, eqf_elim H)
           (λ H, eqf_intro H)

add_rewrite a_eq_not_a a_iff_not_a true_eq_false true_iff_false false_eq_true false_iff_true a_iff_true a_iff_false

theorem not_iff (a b : Bool) : ¬ (a ↔ b) ↔ (¬ a ↔ b)
:= or_elim (em b)
     (λ Hb, calc (¬ (a ↔ b)) =  (¬ (a ↔ true)) : { eqt_intro Hb }
                         ...  =  ¬ a            : { a_iff_true a }
                         ...  = ¬ a ↔ true     : { symm (a_iff_true (¬ a)) }
                         ...  = ¬ a ↔ b        : { symm (eqt_intro Hb) })
     (λ Hnb, calc (¬ (a ↔ b)) = (¬ (a ↔ false)) : { eqf_intro Hnb }
                          ...  = ¬ ¬ a           : { a_iff_false a }
                          ...  = ¬ a ↔ false    : { symm (a_iff_false (¬ a)) }
                          ...  = ¬ a ↔ b        : { symm (eqf_intro Hnb) })

theorem not_iff_elim {a b : Bool} (H : ¬ (a ↔ b)) : (¬ a) ↔ b
:= (not_iff a b) ◂ H

theorem forall_or_distributer {A : (Type U)} (p : Bool) (φ : A → Bool) : (∀ x, p ∨ φ x) = (p ∨ ∀ x, φ x)
:= boolext
     (assume H : (∀ x, p ∨ φ x),
        or_elim (em p)
            (λ Hp  : p,   or_introl Hp (∀ x, φ x))
            (λ Hnp : ¬ p, or_intror p  (take x,
                                             resolve1 (H x) Hnp)))
     (assume H : (p ∨ ∀ x, φ x),
        take x,
            or_elim H
              (λ H1 : p,          or_introl H1 (φ x))
              (λ H2 : (∀ x, φ x), or_intror p  (H2 x)))

theorem forall_or_distributel {A : Type} (p : Bool) (φ : A → Bool) : (∀ x, φ x ∨ p) = ((∀ x, φ x) ∨ p)
:= boolext
     (assume H : (∀ x, φ x ∨ p),
        or_elim (em p)
            (λ Hp  : p,   or_intror (∀ x, φ x) Hp)
            (λ Hnp : ¬ p, or_introl (take x, resolve2 (H x) Hnp) p))
     (assume H : (∀ x, φ x) ∨ p,
        take x,
            or_elim H
              (λ H1 : (∀ x, φ x), or_introl (H1 x) p)
              (λ H2 : p,           or_intror (φ x) H2))

theorem forall_and_distribute {A : (Type U)} (φ ψ : A → Bool) : (∀ x, φ x ∧ ψ x) ↔ (∀ x, φ x) ∧ (∀ x, ψ x)
:= boolext
     (assume H : (∀ x, φ x ∧ ψ x),
        and_intro (take x, and_eliml (H x)) (take x, and_elimr (H x)))
     (assume H : (∀ x, φ x) ∧ (∀ x, ψ x),
        take x, and_intro (and_eliml H x) (and_elimr H x))

theorem exists_and_distributer {A : (Type U)} (p : Bool) (φ : A → Bool) : (∃ x, p ∧ φ x) ↔ p ∧ ∃ x, φ x
:= boolext
     (assume H : (∃ x, p ∧ φ x),
        obtain (w : A) (Hw : p ∧ φ w), from H,
            and_intro (and_eliml Hw) (exists_intro w (and_elimr Hw)))
     (assume H : (p ∧ ∃ x, φ x),
        obtain (w : A) (Hw : φ w), from (and_elimr H),
            exists_intro w (and_intro (and_eliml H) Hw))


theorem exists_or_distribute {A : (Type U)} (φ ψ : A → Bool) : (∃ x, φ x ∨ ψ x) ↔ (∃ x, φ x) ∨ (∃ x, ψ x)
:= boolext
    (assume H : (∃ x, φ x ∨ ψ x),
        obtain (w : A) (Hw : φ w ∨ ψ w), from H,
            or_elim Hw
                (λ Hw1 : φ w, or_introl (exists_intro w Hw1) (∃ x, ψ x))
                (λ Hw2 : ψ w, or_intror (∃ x, φ x) (exists_intro w Hw2)))
    (assume H : (∃ x, φ x) ∨ (∃ x, ψ x),
        or_elim H
            (λ H1 : (∃ x, φ x),
                obtain (w : A) (Hw : φ w), from H1,
                    exists_intro w (or_introl Hw (ψ w)))
            (λ H2 : (∃ x, ψ x),
                obtain (w : A) (Hw : ψ w), from H2,
                    exists_intro w (or_intror (φ w) Hw)))

theorem eq_exists_intro {A : (Type U)} {P Q : A → Bool} (H : ∀ x : A, P x ↔ Q x) : (∃ x : A, P x) ↔ (∃ x : A, Q x)
:= boolext
    (assume Hex, obtain w Pw, from Hex,  exists_intro w ((H w) ◂ Pw))
    (assume Hex, obtain w Qw, from Hex,  exists_intro w ((symm (H w)) ◂ Qw))

theorem not_forall (A : (Type U)) (P : A → Bool) : ¬ (∀ x : A, P x) ↔ (∃ x : A, ¬ P x)
:= boolext
    (assume H, refute (λ N : ¬ (∃ x, ¬ P x),
        absurd (take x, not_not_elim (not_exists_elim N x)) H))
    (assume (H : ∃ x, ¬ P x) (N : ∀ x, P x),
        obtain w Hw, from H,
           absurd (N w) Hw)

theorem not_forall_elim {A : (Type U)} {P : A → Bool} (H : ¬ (∀ x : A, P x)) : ∃ x : A, ¬ P x
:= (not_forall A P) ◂ H

theorem exists_and_distributel {A : (Type U)} (p : Bool) (φ : A → Bool) : (∃ x, φ x ∧ p) ↔ (∃ x, φ x) ∧ p
:= calc (∃ x, φ x ∧ p) = (∃ x, p ∧ φ x)   : eq_exists_intro (λ x, and_comm (φ x) p)
                 ...   = (p ∧ (∃ x, φ x)) : exists_and_distributer p φ
                 ...   = ((∃ x, φ x) ∧ p) : and_comm p (∃ x, φ x)

theorem exists_imp_distribute {A : (Type U)} (φ ψ : A → Bool) : (∃ x, φ x → ψ x) ↔ ((∀ x, φ x) → (∃ x, ψ x))
:= calc (∃ x, φ x → ψ x) = (∃ x, ¬ φ x ∨ ψ x)           : eq_exists_intro (λ x, imp_or (φ x) (ψ x))
                     ...   = (∃ x, ¬ φ x) ∨ (∃ x, ψ x)   : exists_or_distribute _ _
                     ...   = ¬ (∀ x, φ x) ∨ (∃ x, ψ x)   : { symm (not_forall A φ) }
                     ...   = (∀ x, φ x) → (∃ x, ψ x)     : symm (imp_or _ _)

theorem forall_uninhabited {A : (Type U)} {B : A → Bool} (H : ¬ inhabited A) : ∀ x, B x
:= refute (λ N : ¬ (∀ x, B x),
      obtain w Hw, from not_forall_elim N,
         absurd (inhabited_intro w) H)

theorem allext {A : (Type U)} {B C : A → Bool} (H : ∀ x : A, B x = C x) : (∀ x : A, B x) = (∀ x : A, C x)
:= boolext
     (assume Hl, take x, (H x) ◂ (Hl x))
     (assume Hr, take x, (symm (H x)) ◂ (Hr x))

theorem proj1_congr {A : (Type U)} {B : A → (Type U)} {a b : sig x, B x} (H : a = b) : proj1 a = proj1 b
:= subst (refl (proj1 a)) H

theorem proj2_congr {A B : (Type U)} {a b : A # B} (H : a = b) : proj2 a = proj2 b
:= subst (refl (proj2 a)) H

theorem hproj2_congr {A : (Type U)} {B : A → (Type U)} {a b : sig x, B x} (H : a = b) : proj2 a == proj2 b
:= subst (hrefl (proj2 a)) H

definition pair {A : (Type U)} {B : A → (Type U)} (a : A) (b : B a) := tuple (sig x : A, B x) : a, b

-- Up to this point, we proved all theorems using just reflexivity, substitution and case (proof by cases)

-- Function extensionality
axiom funext {A : (Type U)} {B : A → (Type U)} {f g : ∀ x : A, B x} (H : ∀ x : A, f x = g x) : f = g

-- Eta is a consequence of function extensionality
theorem eta {A : (Type U)} {B : A → (Type U)} (f : ∀ x : A, B x) : (λ x : A, f x) = f
:= funext (λ x : A, refl (f x))

-- Epsilon (Hilbert's operator)
variable eps {A : (Type U)} (H : inhabited A) (P : A → Bool) : A
alias ε : eps
axiom eps_ax {A : (Type U)} (H : inhabited A) {P : A → Bool} (a : A) : P a → P (ε H P)

theorem eps_th {A : (Type U)} {P : A → Bool} (a : A) : P a → P (ε (inhabited_intro a) P)
:= assume H : P a, @eps_ax A (inhabited_intro a) P a H

theorem eps_singleton {A : (Type U)} (H : inhabited A) (a : A) : ε H (λ x, x = a) = a
:= let P         :=  λ x, x = a,
       Ha : P a  :=  refl a
   in eps_ax H a Ha

-- A function space (∀ x : A, B x) is inhabited if forall a : A, we have inhabited (B a)
theorem inhabited_dfun {A : (Type U)} {B : A → (Type U)} (Hn : ∀ a, inhabited (B a)) : inhabited (∀ x, B x)
:= inhabited_intro (λ x, ε (Hn x) (λ y, true))

theorem inhabited_fun (A : (Type U)) {B : (Type U)} (H : inhabited B) : inhabited (A → B)
:= inhabited_intro (λ x, ε H (λ y, true))

theorem exists_to_eps {A : (Type U)} {P : A → Bool} (H : ∃ x, P x) : P (ε (inhabited_ex_intro H) P)
:= obtain (w : A) (Hw : P w), from H,
      eps_ax (inhabited_ex_intro H) w Hw

theorem axiom_of_choice {A : (Type U)} {B : A → (Type U)} {R : ∀ x : A, B x → Bool} (H : ∀ x, ∃ y, R x y) : ∃ f, ∀ x, R x (f x)
:= exists_intro
      (λ x, ε (inhabited_ex_intro (H x)) (λ y, R x y)) -- witness for f
      (λ x, exists_to_eps (H x))                      -- proof that witness satisfies ∀ x, R x (f x)

theorem skolem_th {A : (Type U)} {B : A → (Type U)} {P : ∀ x : A, B x → Bool} :
        (∀ x, ∃ y, P x y) ↔ ∃ f, (∀ x, P x (f x))
:= iff_intro
      (λ H : (∀ x, ∃ y, P x y), axiom_of_choice H)
      (λ H : (∃ f, (∀ x, P x (f x))),
             take x, obtain (fw : ∀ x, B x) (Hw : ∀ x, P x (fw x)), from H,
                  exists_intro (fw x) (Hw x))

-- if-then-else expression, we define it using Hilbert's operator
definition ite {A : (Type U)} (c : Bool) (a b : A) : A
:= ε (inhabited_intro a) (λ r, (c → r = a) ∧ (¬ c → r = b))
notation 45 if _ then _ else _ : ite

theorem if_true {A : (Type U)} (a b : A) : (if true then a else b) = a
:= calc (if true then a else b) = ε (inhabited_intro a) (λ r, (true → r = a) ∧ (¬ true → r = b)) : refl (if true then a else b)
                           ...  = ε (inhabited_intro a) (λ r, r = a)                               : by simp
                           ...  = a        : eps_singleton (inhabited_intro a) a

theorem if_false {A : (Type U)} (a b : A) : (if false then a else b) = b
:= calc (if false then a else b) = ε (inhabited_intro a) (λ r, (false → r = a) ∧ (¬ false → r = b)) : refl (if false then a else b)
                            ...  = ε (inhabited_intro a) (λ r, r = b)              : by simp
                            ...  = b                                              : eps_singleton (inhabited_intro a) b

theorem if_a_a {A : (Type U)} (c : Bool) (a: A) : (if c then a else a) = a
:= or_elim (em c)
     (λ H : c,   calc (if c then a else a) = (if true then a else a)  : { eqt_intro H }
                                   ...   = a                          : if_true a a)
     (λ H : ¬ c, calc (if c then a else a) = (if false then a else a) : { eqf_intro H }
                                    ...  = a                          : if_false a a)

add_rewrite if_true if_false if_a_a

theorem if_congr {A : (Type U)} {b c : Bool} {x y u v : A} (H_bc : b = c)
                 (H_xu : ∀ (H_c : c), x = u) (H_yv : ∀ (H_nc : ¬ c), y = v) :
        (if b then x else y) = if c then u else v
:= or_elim (em c)
     (λ H_c : c, calc
          (if b then x else y) = if c then x else y      : { H_bc }
                          ...  = if true then x else y   : { eqt_intro H_c }
                          ...  = x                       : if_true _ _
                          ...  = u                       : H_xu H_c
                          ...  = if true then u else v   : symm (if_true _ _)
                          ...  = if c then u else v      : { symm (eqt_intro H_c) })
     (λ H_nc : ¬ c, calc
          (if b then x else y) = if c then x else y      : { H_bc }
                          ...  = if false then x else y  : { eqf_intro H_nc }
                          ...  = y                       : if_false _ _
                          ...  = v                       : H_yv H_nc
                          ...  = if false then u else v  : symm (if_false _ _)
                          ...  = if c then u else v      : { symm (eqf_intro H_nc) })

theorem if_imp_then {a b c : Bool} (H : if a then b else c)  : a → b
:= assume Ha : a, eqt_elim (calc   b = if true then b else c : symm (if_true b c)
                                 ... = if a then b else c    : { symm (eqt_intro Ha) }
                                 ... = true                  : eqt_intro H)

theorem if_imp_else {a b c : Bool} (H : if a then b else c) : ¬ a → c
:= assume Hna : ¬ a, eqt_elim (calc   c = if false then b else c : symm (if_false b c)
                                    ... = if a then b else c     : { symm (eqf_intro Hna) }
                                    ... = true                   : eqt_intro H)

theorem app_if_distribute {A B : (Type U)} (c : Bool) (f : A → B) (a b : A) : f (if c then a else b) = if c then f a else f b
:= or_elim (em c)
     (λ Hc : c , calc
          f (if c then a else b) = f (if true then a else b)    : { eqt_intro Hc }
                            ...  = f a                          : { if_true a b }
                            ...  = if true then f a else f b    : symm (if_true (f a) (f b))
                            ...  = if c then f a else f b       : { symm (eqt_intro Hc) })
     (λ Hnc : ¬ c, calc
          f (if c then a else b) = f (if false then a else b)   : { eqf_intro Hnc }
                            ...  = f b                          : { if_false a b }
                            ...  = if false then f a else f b   : symm (if_false (f a) (f b))
                            ...  = if c then f a else f b       : { symm (eqf_intro Hnc) })

theorem eq_if_distributer {A : (Type U)} (c : Bool) (a b v : A) : (v = (if c then a else b)) = if c then v = a else v = b
:= app_if_distribute c (eq v) a b

theorem eq_if_distributel {A : (Type U)} (c : Bool) (a b v : A) : ((if c then a else b) = v) = if c then a = v else b = v
:= app_if_distribute c (λ x, x = v) a b

set_opaque exists  true
set_opaque not     true
set_opaque or      true
set_opaque and     true
set_opaque implies true
set_opaque ite     true
set_opaque eq      true

definition injective {A B : (Type U)} (f : A → B)  := ∀ x1 x2, f x1 = f x2 → x1 = x2
definition non_surjective {A B : (Type U)} (f : A → B) := ∃ y, ∀ x, ¬ f x = y

-- The set of individuals, we need to assert the existence of one infinite set
variable ind : Type
-- ind is infinite, i.e., there is a function f s.t. f is injective, and not surjective
axiom infinity : ∃ f : ind → ind, injective f ∧ non_surjective f

-- Pair extensionality
axiom pairext {A : (Type U)} {B : A → (Type U)} (a b : sig x, B x)
              (H1 : proj1 a = proj1 b) (H2 : proj2 a == proj2 b)
              : a = b

theorem pair_proj_eq {A : (Type U)} {B : A → (Type U)} (a : sig x, B x) : pair (proj1 a) (proj2 a) = a
:= have Heq1 : proj1 (pair (proj1 a) (proj2 a)) = proj1 a,
     from refl (proj1 a),
   have Heq2 : proj2 (pair (proj1 a) (proj2 a)) == proj2 a,
     from hrefl (proj2 a),
   show pair (proj1 a) (proj2 a) = a,
     from pairext (pair (proj1 a) (proj2 a)) a Heq1 Heq2

theorem pair_congr {A : (Type U)} {B : A → (Type U)} {a a' : A} {b : B a} {b' : B a'} (Ha : a = a') (Hb : b == b')
                   : (pair a b) = (pair a' b')
:= have Heq1 : proj1 (pair a b) = proj1 (pair a' b'),
     from Ha,
   have Heq2 : proj2 (pair a b) == proj2 (pair a' b'),
     from Hb,
   show (pair a b) = (pair a' b'),
     from pairext (pair a b) (pair a' b') Heq1 Heq2

theorem pairext_proj {A B : (Type U)} {p : A # B} {a : A} {b : B} (H1 : proj1 p = a) (H2 : proj2 p = b) : p = (pair a b)
:= pairext p (pair a b) H1 (to_heq H2)

theorem hpairext_proj {A : (Type U)} {B : A → (Type U)} {p : sig x, B x} {a : A} {b : B a}
                      (H1 : proj1 p = a) (H2 : proj2 p == b) : p = (pair a b)
:= pairext p (pair a b) H1 H2

-- Heterogeneous equality axioms and theorems

-- We can "type-cast" an A expression into a B expression, if we can prove that A == B
-- Remark: we use A == B instead of A = B, because A = B would be type incorrect.
-- A = B is actually (@eq (Type U) A B), which is type incorrect because
-- the first argument of eq must have type (Type U) and the type of (Type U) is (Type U+1)
variable cast {A B : (Type U+1)} : A == B → A → B

axiom cast_heq {A B : (Type U+1)} (H : A == B) (a : A) : cast H a == a

-- Heterogeneous equality satisfies the usual properties: symmetry, transitivity, congruence, function extensionality, ...

-- Heterogeneous version of subst
axiom hsubst {A B : (Type U+1)} {a : A} {b : B} (P : ∀ T : (Type U+1), T → Bool) : P A a → a == b → P B b

theorem hsymm {A B : (Type U+1)} {a : A} {b : B} (H : a == b) : b == a
:= hsubst (λ (T : (Type U+1)) (x : T), x == a) (hrefl a) H

theorem htrans {A B C : (Type U+1)} {a : A} {b : B} {c : C} (H1 : a == b) (H2 : b == c) : a == c
:= hsubst (λ (T : (Type U+1)) (x : T), a == x) H1 H2

axiom hcongr {A A' : (Type U+1)} {B : A → (Type U+1)} {B' : A' → (Type U+1)} {f : ∀ x, B x} {f' : ∀ x, B' x} {a : A} {a' : A'} :
      f == f' → a == a' → f a == f' a'

axiom hfunext {A A' : (Type U+1)} {B : A → (Type U+1)} {B' : A' → (Type U+1)} {f : ∀ x, B x} {f' : ∀ x, B' x} :
      A == A' → (∀ x x', x == x' → f x == f' x') → f == f'

axiom hpiext {A A' : (Type U+1)} {B : A → (Type U+1)} {B' : A' → (Type U+1)} :
      A == A' → (∀ x x', x == x' → B x == B' x') → (∀ x, B x) == (∀ x, B' x)

axiom hsigext {A A' : (Type U+1)} {B : A → (Type U+1)} {B' : A' → (Type U+1)} :
      A == A' → (∀ x x', x == x' → B x == B' x') → (sig x, B x) == (sig x, B' x)

-- Heterogeneous version of the allext theorem
theorem hallext {A A' : (Type U+1)} {B : A → Bool} {B' : A' → Bool}
                (Ha : A == A') (Hb : ∀ x x', x == x' → B x = B' x') : (∀ x, B x) = (∀ x, B' x)
:= to_eq (hpiext Ha (λ x x' Heq, to_heq (Hb x x' Heq)))

-- Simpler version of hfunext axiom, we use it to build proofs
theorem hsfunext {A : (Type U)} {B B' : A → (Type U)} {f : ∀ x, B x} {f' : ∀ x, B' x} :
      (∀ x, f x == f' x) → f == f'
:= λ Hb,
     hfunext (hrefl A) (λ (x x' : A) (Heq : x == x'),
                   let s1 : f x   == f' x  := Hb x,
                       s2 : f' x  == f' x' := hcongr (hrefl f') Heq
                   in htrans s1 s2)

theorem heq_congr {A B : (Type U)} {a a' : A} {b b' : B} (H1 : a = a') (H2 : b = b') : (a == b) = (a' == b')
:= calc (a == b) = (a' == b)  : { H1 }
            ...  = (a' == b') : { H2 }

theorem hheq_congr {A A' B B' : (Type U+1)} {a : A} {a' : A'} {b : B} {b' : B'} (H1 : a == a') (H2 : b == b') : (a == b) = (a' == b')
:= have Heq1 : (a == b) = (a' == b),
     from (hsubst (λ (T : (Type U+1)) (x : T), (a == b)  = (x  == b)) (refl (a == b))  H1),
   have Heq2 : (a' == b) = (a' == b'),
     from (hsubst (λ (T : (Type U+1)) (x : T), (a' == b) = (a' == x)) (refl (a' == b)) H2),
   show (a == b) = (a' == b'),
     from trans Heq1 Heq2

theorem type_eq {A B : (Type U)} {a : A} {b : B} (H : a == b) : A == B
:= hsubst (λ (T : (Type U+1)) (x : T), A == T) (hrefl A) H

-- Some theorems that are useful for applying simplifications.
theorem cast_eq {A : (Type U)} (H : A == A) (a : A) : cast H a = a
:= to_eq (cast_heq H a)

theorem cast_trans {A B C : (Type U)} (Hab : A == B) (Hbc : B == C) (a : A) : cast Hbc (cast Hab a) = cast (htrans Hab Hbc) a
:= have Heq1 : cast Hbc (cast Hab a)   == cast Hab a,
     from cast_heq Hbc (cast Hab a),
   have Heq2 : cast Hab a              == a,
     from cast_heq Hab a,
   have Heq3 : cast (htrans Hab Hbc) a == a,
     from cast_heq (htrans Hab Hbc) a,
   show cast Hbc (cast Hab a) = cast (htrans Hab Hbc) a,
     from to_eq (htrans (htrans Heq1 Heq2) (hsymm Heq3))

theorem cast_pull {A : (Type U)} {B B' : A → (Type U)}
                 (f : ∀ x, B x) (a : A) (Hb : (∀ x, B x) == (∀ x, B' x)) (Hba : (B a) == (B' a)) :
      cast Hb f a = cast Hba (f a)
:= have s1 : cast Hb f a    == f a,
     from hcongr (cast_heq Hb f) (hrefl a),
   have s2 : cast Hba (f a) == f a,
     from cast_heq Hba (f a),
   show cast Hb f a = cast Hba (f a),
     from to_eq (htrans s1 (hsymm s2))

-- Proof irrelevance is true in the set theoretic model we have for Lean.
axiom proof_irrel {a : Bool} (H1 H2 : a) : H1 = H2

-- A more general version of proof_irrel that can be be derived using proof_irrel, heq axioms and boolext/iff_intro
theorem hproof_irrel {a b : Bool} (H1 : a) (H2 : b) : H1 == H2
:= let Hab       : a == b                := to_heq (iff_intro (assume Ha, H2) (assume Hb, H1)),
       H1b       : b                     := cast Hab H1,
       H1_eq_H1b : H1 == H1b             := hsymm (cast_heq Hab H1),
       H1b_eq_H2 : H1b == H2             := to_heq (proof_irrel H1b H2)
   in  htrans H1_eq_H1b H1b_eq_H2
