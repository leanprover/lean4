import macros

universe U ≥ 1

variable Bool : Type
-- The following builtin declarations can be removed as soon as Lean supports inductive datatypes and match expressions
builtin true : Bool
builtin false : Bool

definition TypeU := (Type U)

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

definition iff (a b : Bool) := a == b

infixr 25 <-> : iff
infixr 25 ↔   : iff

-- The Lean parser has special treatment for the constant exists.
-- It allows us to write
--      exists x y : A, P x y   and    ∃ x y : A, P x y
-- as syntax sugar for
--      exists A (fun x : A, exists A (fun y : A, P x y))
-- That is, it treats the exists as an extra binder such as fun and forall.
-- It also provides an alias (Exists) that should be used when we
-- want to treat exists as a constant.
definition Exists (A : TypeU) (P : A → Bool) := ¬ (∀ x : A, ¬ (P x))

definition eq {A : TypeU} (a b : A) := a == b

infix 50 = : eq

definition neq {A : TypeU} (a b : A) := ¬ (a = b)

infix 50 ≠ : neq

theorem em (a : Bool) : a ∨ ¬ a
:= assume Hna : ¬ a, Hna

axiom case (P : Bool → Bool) (H1 : P true) (H2 : P false) (a : Bool) : P a

axiom refl {A : TypeU} (a : A) : a = a

axiom subst {A : TypeU} {a b : A} {P : A → Bool} (H1 : P a) (H2 : a = b) : P b

-- Function extensionality
axiom funext {A : TypeU} {B : A → TypeU} {f g : ∀ x : A, B x} (H : ∀ x : A, f x == g x) : f == g

-- Forall extensionality
axiom allext {A : TypeU} {B C : A → TypeU} (H : ∀ x : A, B x == C x) : (∀ x : A, B x) == (∀ x : A, C x)

-- Alias for subst where we can provide P explicitly, but keep A,a,b implicit
theorem substp {A : TypeU} {a b : A} (P : A → Bool) (H1 : P a) (H2 : a = b) : P b
:= subst H1 H2

-- We will mark not as opaque later
theorem not_intro {a : Bool} (H : a → false) : ¬ a
:= H

theorem eta {A : TypeU} {B : A → TypeU} (f : ∀ x : A, B x) : (λ x : A, f x) = f
:= funext (λ x : A, refl (f x))

theorem trivial : true
:= refl true

theorem absurd {a : Bool} (H1 : a) (H2 : ¬ a) : false
:= H2 H1

theorem eqmp {a b : Bool} (H1 : a = b) (H2 : a) : b
:= subst H2 H1

infixl 100 <| : eqmp
infixl 100 ◂  : eqmp

theorem boolcomplete (a : Bool) : a = true ∨ a = false
:= case (λ x, x = true ∨ x = false) trivial trivial a

theorem false_elim (a : Bool) (H : false) : a
:= case (λ x, x) trivial H a

theorem imp_trans {a b c : Bool} (H1 : a → b) (H2 : b → c) : a → c
:= assume Ha, H2 (H1 Ha)

theorem imp_eq_trans {a b c : Bool} (H1 : a → b) (H2 : b = c) : a → c
:= assume Ha, H2 ◂ (H1 Ha)

theorem eq_imp_trans {a b c : Bool} (H1 : a = b) (H2 : b → c) : a → c
:= assume Ha, H2 (H1 ◂ Ha)

theorem not_not_eq (a : Bool) : ¬ ¬ a ↔ a
:= case (λ x, ¬ ¬ x ↔ x) trivial trivial a

theorem not_not_elim {a : Bool} (H : ¬ ¬ a) : a
:= (not_not_eq a) ◂ H

theorem mt {a b : Bool} (H1 : a → b) (H2 : ¬ b) : ¬ a
:= assume Ha : a, absurd (H1 Ha) H2

theorem contrapos {a b : Bool} (H : a → b) : ¬ b → ¬ a
:= assume Hnb : ¬ b, mt H Hnb

theorem absurd_elim {a : Bool} (b : Bool) (H1 : a) (H2 : ¬ a) : b
:= false_elim b (absurd H1 H2)

theorem not_imp_eliml {a b : Bool} (Hnab : ¬ (a → b)) : a
:= not_not_elim
      (have ¬ ¬ a :
          assume Hna : ¬ a, absurd (assume Ha : a, absurd_elim b Ha Hna)
                                   Hnab)

theorem not_imp_elimr {a b : Bool} (H : ¬ (a → b)) : ¬ b
:= assume Hb : b, absurd (assume Ha : a, Hb)
                         H

theorem resolve1 {a b : Bool} (H1 : a ∨ b) (H2 : ¬ a) : b
:= H1 H2

-- Recall that and is defined as ¬ (a → ¬ b)
theorem and_intro {a b : Bool} (H1 : a) (H2 : b) : a ∧ b
:= assume H : a → ¬ b, absurd H2 (H H1)

theorem and_eliml {a b : Bool} (H : a ∧ b) : a
:= not_imp_eliml H

theorem and_elimr {a b : Bool} (H : a ∧ b) : b
:= not_not_elim (not_imp_elimr H)

-- Recall that or is defined as ¬ a → b
theorem or_introl {a : Bool} (H : a) (b : Bool) : a ∨ b
:= assume H1 : ¬ a, absurd_elim b H H1

theorem or_intror {b : Bool} (a : Bool) (H : b) : a ∨ b
:= assume H1 : ¬ a, H

theorem or_elim {a b c : Bool} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
:= not_not_elim
     (assume H : ¬ c,
        absurd (have c : H3 (have b : resolve1 H1 (have ¬ a : (mt (assume Ha : a, H2 Ha) H))))
               H)

theorem refute {a : Bool} (H : ¬ a → false) : a
:= or_elim (em a) (λ H1 : a, H1) (λ H1 : ¬ a, false_elim a (H H1))

theorem symm {A : TypeU} {a b : A} (H : a = b) : b = a
:= subst (refl a) H

theorem trans {A : TypeU} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c
:= subst H1 H2

infixl 100 ⋈ : trans

theorem ne_symm {A : TypeU} {a b : A} (H : a ≠ b) : b ≠ a
:= assume H1 : b = a, H (symm H1)

theorem eq_ne_trans {A : TypeU} {a b c : A} (H1 : a = b) (H2 : b ≠ c) : a ≠ c
:= subst H2 (symm H1)

theorem ne_eq_trans {A : TypeU} {a b c : A} (H1 : a ≠ b) (H2 : b = c) : a ≠ c
:= subst H1 H2

theorem heq_congr {A : TypeU} {a b c d : A} (H1 : a == c) (H2 : b == d) : (a == b) = (c == d)
:= calc (a == b) = (c == b) : { H1 }
             ... = (c == d) : { H2 }

theorem heq_congrl {A : TypeU} {a : A} (b : A) {c : A} (H : a == c) : (a == b) = (c == b)
:= heq_congr H (refl b)

theorem heq_congrr {A : TypeU} (a : A) {b d : A} (H : b == d) : (a == b) = (a == d)
:= heq_congr (refl a) H

theorem eqt_elim {a : Bool} (H : a = true) : a
:= (symm H) ◂ trivial

theorem eqf_elim {a : Bool} (H : a = false) : ¬ a
:= not_intro (λ Ha : a, H ◂ Ha)

theorem congr1 {A : TypeU} {B : A → TypeU} {f g : ∀ x : A, B x} (a : A) (H : f = g) : f a = g a
:= substp (fun h : (∀ x : A, B x), f a = h a) (refl (f a)) H

-- We must use heterogenous equality in this theorem because (f a) : (B a) and (f b) : (B b)
theorem congr2 {A : TypeU} {B : A → TypeU} {a b : A} (f : ∀ x : A, B x) (H : a = b) : f a == f b
:= substp (fun x : A, f a == f x) (refl (f a)) H

theorem congr {A : TypeU} {B : A → TypeU} {f g : ∀ x : A, B x} {a b : A} (H1 : f = g) (H2 : a = b) : f a == g b
:= subst (congr2 f H2) (congr1 b H1)

-- Simpler version of congr2 theorem for arrows (i.e., non-dependent types)
theorem scongr2 {A B : TypeU} {a b : A} (f : A → B) (H : a = b) : f a = f b
:= substp (fun x : A, f a = f x) (refl (f a)) H

-- Simpler version of congr theorem for arrows (i.e., non-dependent types)
theorem scongr {A B : TypeU} {f g : A → B} {a b : A} (H1 : f = g) (H2 : a = b) : f a = g b
:= subst (scongr2 f H2) (congr1 b H1)

-- Recall that exists is defined as ¬ ∀ x : A, ¬ P x
theorem exists_elim {A : TypeU} {P : A → Bool} {B : Bool} (H1 : Exists A P) (H2 : ∀ (a : A) (H : P a), B) : B
:= refute (λ R : ¬ B,
             absurd (take a : A, mt (assume H : P a, H2 a H) R)
                    H1)

theorem exists_intro {A : TypeU} {P : A → Bool} (a : A) (H : P a) : Exists A P
:= assume H1 : (∀ x : A, ¬ P x),
      absurd H (H1 a)

theorem boolext {a b : Bool} (Hab : a → b) (Hba : b → a) : a = b
:= or_elim (boolcomplete a)
       (λ Hat : a = true,  or_elim (boolcomplete b)
           (λ Hbt : b = true,  trans Hat (symm Hbt))
           (λ Hbf : b = false, false_elim (a = b) (subst (Hab (eqt_elim Hat)) Hbf)))
       (λ Haf : a = false, or_elim (boolcomplete b)
           (λ Hbt : b = true,  false_elim (a = b) (subst (Hba (eqt_elim Hbt)) Haf))
           (λ Hbf : b = false, trans Haf (symm Hbf)))

theorem iff_intro {a b : Bool} (Hab : a → b) (Hba : b → a) : a = b
:= boolext Hab Hba

theorem eqt_intro {a : Bool} (H : a) : a = true
:= boolext (assume H1 : a,    trivial)
           (assume H2 : true, H)

theorem eqf_intro {a : Bool} (H : ¬ a) : a = false
:= boolext (assume H1 : a,     absurd H1 H)
           (assume H2 : false, false_elim a H2)

theorem neq_elim {A : TypeU} {a b : A} (H : a ≠ b) : a = b ↔ false
:= eqf_intro H

theorem or_comm (a b : Bool) : a ∨ b ↔ b ∨ a
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
:= (or_comm false a) ⋈ (or_falsel a)

theorem or_truel (a : Bool) : true ∨ a ↔ true
:= eqt_intro (case (λ x : Bool, true ∨ x) trivial trivial a)

theorem or_truer (a : Bool) : a ∨ true ↔ true
:= (or_comm a true) ⋈ (or_truel a)

theorem or_tauto (a : Bool) : a ∨ ¬ a ↔ true
:= eqt_intro (em a)

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
:= (and_comm false a) ⋈ (and_falsel a)

theorem and_absurd (a : Bool) : a ∧ ¬ a ↔ false
:= boolext (assume H, absurd (and_eliml H) (and_elimr H))
           (assume H, false_elim (a ∧ ¬ a) H)

theorem imp_truer (a : Bool) : (a → true) ↔ true
:= case (λ x, (x → true) ↔ true) trivial trivial a

theorem imp_truel (a : Bool) : (true → a) ↔ a
:= case (λ x, (true → x) ↔ x) trivial trivial a

theorem imp_falser (a : Bool) : (a → false) ↔ ¬ a
:= refl _

theorem imp_falsel (a : Bool) : (false → a) ↔ true
:= case (λ x, (false → x) ↔ true) trivial trivial a

theorem not_and (a b : Bool) : ¬ (a ∧ b) ↔ ¬ a ∨ ¬ b
:= case (λ x, ¬ (x ∧ b) ↔ ¬ x ∨ ¬ b)
        (case (λ y, ¬ (true ∧ y) ↔ ¬ true ∨ ¬ y)   trivial trivial b)
        (case (λ y, ¬ (false ∧ y) ↔ ¬ false ∨ ¬ y) trivial trivial b)
        a

theorem not_and_elim {a b : Bool} (H : ¬ (a ∧ b)) : ¬ a ∨ ¬ b
:= (not_and a b) ◂ H

theorem not_or (a b : Bool) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b
:= case (λ x, ¬ (x ∨ b) ↔ ¬ x ∧ ¬ b)
        (case (λ y, ¬ (true ∨ y) ↔ ¬ true ∧ ¬ y)   trivial trivial b)
        (case (λ y, ¬ (false ∨ y) ↔ ¬ false ∧ ¬ y) trivial trivial b)
        a

theorem not_or_elim {a b : Bool} (H : ¬ (a ∨ b)) : ¬ a ∧ ¬ b
:= (not_or a b) ◂ H

theorem not_iff (a b : Bool) : ¬ (a ↔ b) ↔ (¬ a ↔ b)
:= case (λ x, ¬ (x ↔ b) ↔ ((¬ x) ↔ b))
        (case (λ y, ¬ (true ↔ y) ↔ ((¬ true) ↔ y)) trivial trivial b)
        (case (λ y, ¬ (false ↔ y) ↔ ((¬ false) ↔ y)) trivial trivial b)
        a

theorem not_iff_elim {a b : Bool} (H : ¬ (a ↔ b)) : (¬ a) ↔ b
:= (not_iff a b) ◂ H

theorem not_implies (a b : Bool) : ¬ (a → b) ↔ a ∧ ¬ b
:= case (λ x, ¬ (x → b) ↔ x ∧ ¬ b)
        (case (λ y, ¬ (true → y) ↔ true ∧ ¬ y) trivial trivial b)
        (case (λ y, ¬ (false → y) ↔ false ∧ ¬ y) trivial trivial b)
        a

theorem not_implies_elim {a b : Bool} (H : ¬ (a → b)) : a ∧ ¬ b
:= (not_implies a b) ◂ H

theorem not_congr {a b : Bool} (H : a ↔ b) : ¬ a ↔ ¬ b
:= congr2 not H

theorem eq_exists_intro {A : (Type U)} {P Q : A → Bool} (H : ∀ x : A, P x ↔ Q x) : (∃ x : A, P x) ↔ (∃ x : A, Q x)
:= congr2 (Exists A) (funext H)

theorem not_forall (A : (Type U)) (P : A → Bool) : ¬ (∀ x : A, P x) ↔ (∃ x : A, ¬ P x)
:= calc (¬ ∀ x : A, P x) = ¬ ∀ x : A, ¬ ¬ P x : not_congr (allext (λ x : A, symm (not_not_eq (P x))))
              ...        = ∃ x : A, ¬ P x     : refl (∃ x : A, ¬ P x)

theorem not_forall_elim {A : (Type U)} {P : A → Bool} (H : ¬ (∀ x : A, P x)) : ∃ x : A, ¬ P x
:= (not_forall A P) ◂ H

theorem not_exists (A : (Type U)) (P : A → Bool) : ¬ (∃ x : A, P x) ↔ (∀ x : A, ¬ P x)
:= calc (¬ ∃ x : A, P x) = ¬ ¬ ∀ x : A, ¬ P x : refl (¬ ∃ x : A, P x)
                     ... = ∀ x : A, ¬ P x     : not_not_eq (∀ x : A, ¬ P x)

theorem not_exists_elim {A : (Type U)} {P : A → Bool} (H : ¬ ∃ x : A, P x) : ∀ x : A, ¬ P x
:= (not_exists A P) ◂ H

theorem exists_unfold1 {A : TypeU} {P : A → Bool} (a : A) (H : ∃ x : A, P x) : P a ∨ (∃ x : A, x ≠ a ∧ P x)
:= exists_elim H
     (λ (w : A) (H1 : P w),
        or_elim (em (w = a))
          (λ Heq : w = a, or_introl (subst H1 Heq) (∃ x : A, x ≠ a ∧ P x))
          (λ Hne : w ≠ a, or_intror (P a) (exists_intro w (and_intro Hne H1))))

theorem exists_unfold2 {A : TypeU} {P : A → Bool} (a : A) (H : P a ∨ (∃ x : A, x ≠ a ∧ P x)) : ∃ x : A, P x
:= or_elim H
      (λ H1 : P a, exists_intro a H1)
      (λ H2 : (∃ x : A, x ≠ a ∧ P x),
          exists_elim H2
               (λ (w : A) (Hw : w ≠ a ∧ P w),
                  exists_intro w (and_elimr Hw)))

theorem exists_unfold {A : TypeU} (P : A → Bool) (a : A) : (∃ x : A, P x) ↔ (P a ∨ (∃ x : A, x ≠ a ∧ P x))
:= boolext (assume H : (∃ x : A, P x),                 exists_unfold1 a H)
           (assume H : (P a ∨ (∃ x : A, x ≠ a ∧ P x)), exists_unfold2 a H)


-- Remark: ordered rewriting + assoc + comm + left_comm sorts a term lexicographically
theorem left_comm {A : TypeU} {R : A -> A -> A} (comm : ∀ x y, R x y = R y x) (assoc : ∀ x y z, R (R x y) z = R x (R y z)) :
        ∀ x y z, R x (R y z) = R y (R x z)
:= take x y z, calc R x (R y z) = R (R x y) z : symm (assoc x y z)
                         ...    = R (R y x) z : { comm x y }
                         ...    = R y (R x z) : assoc y x z

theorem and_left_comm (a b c : Bool) : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c)
:= left_comm and_comm and_assoc a b c

theorem or_left_comm (a b c : Bool) : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c)
:= left_comm or_comm or_assoc a b c

-- Congruence theorems for contextual simplification

-- Simplify a → b, by first simplifying a to c using the fact that ¬ b is true, and then
-- b to d using the fact that c is true
theorem imp_congrr {a b c d : Bool} (H_ac : ∀ (H_nb : ¬ b), a = c) (H_bd : ∀ (H_c : c), b = d) : (a → b) = (c → d)
:= or_elim (em b)
      (λ H_b : b,
          or_elim (em c)
             (λ H_c : c,
                 calc (a → b) = (a → true)  : { eqt_intro H_b }
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
theorem imp_congrl {a b c d : Bool} (H_ac : ∀ (H_nd : ¬ d), a = c) (H_bd : ∀ (H_a : a), b = d) : (a → b) = (c → d)
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
theorem or_congrl {a b c d : Bool} (H_ac : ∀ (H_nd : ¬ d), a = c) (H_bd : ∀ (H_na : ¬ a), b = d) : a ∨ b ↔ c ∨ d
:= imp_congrl (λ H_nd : ¬ d, congr2 not (H_ac H_nd)) H_bd
-- (Common case) simplify a to c, and then b to d using the fact that ¬ c is true
theorem or_congr {a b c d : Bool} (H_ac : a = c) (H_bd : ∀ (H_nc : ¬ c), b = d) : a ∨ b ↔ c ∨ d
:= or_congrr (λ H, H_ac) H_bd

-- In the following theorems we are using the fact hat a ∧ b is defined as ¬ (a → ¬ b)
theorem and_congrr {a b c d : Bool} (H_ac : ∀ (H_b : b), a = c) (H_bd : ∀ (H_c : c), b = d) : a ∧ b ↔ c ∧ d
:= congr2 not (imp_congrr (λ (H_nnb : ¬ ¬ b), H_ac (not_not_elim H_nnb)) (λ H_c : c, congr2 not (H_bd H_c)))
theorem and_congrl {a b c d : Bool} (H_ac : ∀ (H_d : d), a = c) (H_bd : ∀ (H_a : a), b = d) : a ∧ b ↔ c ∧ d
:= congr2 not (imp_congrl (λ (H_nnd : ¬ ¬ d), H_ac (not_not_elim H_nnd)) (λ H_a : a, congr2 not (H_bd H_a)))
-- (Common case) simplify a to c, and then b to d using the fact that c is true
theorem and_congr {a b c d : Bool} (H_ac : a = c) (H_bd : ∀ (H_c : c), b = d) : a ∧ b ↔ c ∧ d
:= and_congrr (λ H, H_ac) H_bd

theorem forall_or_distributer {A : TypeU} (p : Bool) (φ : A → Bool) : (∀ x, p ∨ φ x) ↔ p ∨ ∀ x, φ x
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

theorem forall_or_distributel {A : TypeU} (p : Bool) (φ : A → Bool) : (∀ x, φ x ∨ p) ↔ (∀ x, φ x) ∨ p
:= calc (∀ x, φ x ∨ p) = (∀ x, p ∨ φ x)   : allext (λ x, or_comm (φ x) p)
                  ...  = (p ∨ ∀ x, φ x)   : forall_or_distributer p φ
                  ...  = ((∀ x, φ x) ∨ p) : or_comm p (∀ x, φ x)

theorem forall_and_distribute {A : TypeU} (φ ψ : A → Bool) : (∀ x, φ x ∧ ψ x) ↔ (∀ x, φ x) ∧ (∀ x, ψ x)
:= boolext
     (assume H : (∀ x, φ x ∧ ψ x),
        and_intro (take x, and_eliml (H x)) (take x, and_elimr (H x)))
     (assume H : (∀ x, φ x) ∧ (∀ x, ψ x),
        take x, and_intro (and_eliml H x) (and_elimr H x))

theorem exists_and_distributer {A : TypeU} (p : Bool) (φ : A → Bool) : (∃ x, p ∧ φ x) ↔ p ∧ ∃ x, φ x
:= boolext
     (assume H : (∃ x, p ∧ φ x),
        obtain (w : A) (Hw : p ∧ φ w), from H,
            and_intro (and_eliml Hw) (exists_intro w (and_elimr Hw)))
     (assume H : (p ∧ ∃ x, φ x),
        obtain (w : A) (Hw : φ w), from (and_elimr H),
            exists_intro w (and_intro (and_eliml H) Hw))

theorem exists_and_distributel {A : TypeU} (p : Bool) (φ : A → Bool) : (∃ x, φ x ∧ p) ↔ (∃ x, φ x) ∧ p
:= calc (∃ x, φ x ∧ p) = (∃ x, p ∧ φ x)   : eq_exists_intro (λ x, and_comm (φ x) p)
                 ...   = (p ∧ (∃ x, φ x)) : exists_and_distributer p φ
                 ...   = ((∃ x, φ x) ∧ p) : and_comm p (∃ x, φ x)

theorem exists_or_distribute {A : TypeU} (φ ψ : A → Bool) : (∃ x, φ x ∨ ψ x) ↔ (∃ x, φ x) ∨ (∃ x, ψ x)
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

set_opaque exists  true
set_opaque not     true
set_opaque or      true
set_opaque and     true
set_opaque implies true