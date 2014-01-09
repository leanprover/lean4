import macros

universe U ≥ 1

variable Bool : Type
-- The following builtin declarations can be removed as soon as Lean supports inductive datatypes and match expressions
builtin true : Bool
builtin false : Bool
builtin if {A : (Type U)} : Bool → A → A → A

definition TypeU := (Type U)

definition not (a : Bool) := a → false

notation 40 ¬ _ : not

definition or (a b : Bool) := ¬ a → b

infixr 30 || : or
infixr 30 \/ : or
infixr 30 ∨  : or

definition and (a b : Bool) := ¬ (a → ¬ b)

definition implies (a b : Bool) := a → b

infixr 35 && : and
infixr 35 /\ : and
infixr 35 ∧  : and

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

definition neq {A : TypeU} (a b : A) := ¬ (a == b)

infix 50 ≠ : neq

theorem em (a : Bool) : a ∨ ¬ a
:= λ Hna : ¬ a, Hna

axiom case (P : Bool → Bool) (H1 : P true) (H2 : P false) (a : Bool) : P a

axiom refl {A : TypeU} (a : A) : a == a

axiom subst {A : TypeU} {a b : A} {P : A → Bool} (H1 : P a) (H2 : a == b) : P b

-- Function extensionality
axiom funext {A : TypeU} {B : A → TypeU} {f g : ∀ x : A, B x} (H : ∀ x : A, f x == g x) : f == g

-- Forall extensionality
axiom allext {A : TypeU} {B C : A → TypeU} (H : ∀ x : A, B x == C x) : (∀ x : A, B x) == (∀ x : A, C x)

-- Alias for subst where we can provide P explicitly, but keep A,a,b implicit
definition substp {A : TypeU} {a b : A} (P : A → Bool) (H1 : P a) (H2 : a == b) : P b
:= subst H1 H2

theorem eta {A : TypeU} {B : A → TypeU} (f : ∀ x : A, B x) : (λ x : A, f x) == f
:= funext (λ x : A, refl (f x))

theorem trivial : true
:= refl true

theorem absurd {a : Bool} (H1 : a) (H2 : ¬ a) : false
:= H2 H1

theorem eqmp {a b : Bool} (H1 : a == b) (H2 : a) : b
:= subst H2 H1

infixl 100 <| : eqmp
infixl 100 ◂  : eqmp

theorem boolcomplete (a : Bool) : a == true ∨ a == false
:= case (λ x, x == true ∨ x == false) trivial trivial a

theorem false_elim (a : Bool) (H : false) : a
:= case (λ x, x) trivial H a

theorem imp_trans {a b c : Bool} (H1 : a → b) (H2 : b → c) : a → c
:= λ Ha, H2 (H1 Ha)

theorem imp_eq_trans {a b c : Bool} (H1 : a → b) (H2 : b == c) : a → c
:= λ Ha, H2 ◂ (H1 Ha)

theorem eq_imp_trans {a b c : Bool} (H1 : a == b) (H2 : b → c) : a → c
:= λ Ha, H2 (H1 ◂ Ha)

theorem not_not_eq (a : Bool) : (¬ ¬ a) == a
:= case (λ x, (¬ ¬ x) == x) trivial trivial a

theorem not_not_elim {a : Bool} (H : ¬ ¬ a) : a
:= (not_not_eq a) ◂ H

theorem mt {a b : Bool} (H1 : a → b) (H2 : ¬ b) : ¬ a
:= λ Ha, absurd (H1 Ha) H2

theorem contrapos {a b : Bool} (H : a → b) : ¬ b → ¬ a
:= λ Hnb : ¬ b, mt H Hnb

theorem absurd_elim {a : Bool} (b : Bool) (H1 : a) (H2 : ¬ a) : b
:= false_elim b (absurd H1 H2)

theorem not_imp_eliml {a b : Bool} (Hnab : ¬ (a → b)) : a
:= not_not_elim
      (have ¬ ¬ a :
          λ Hna : ¬ a, absurd (λ Ha : a, absurd_elim b Ha Hna)
                              Hnab)

theorem not_imp_elimr {a b : Bool} (H : ¬ (a → b)) : ¬ b
:= λ Hb : b, absurd (λ Ha : a, Hb)
                    H

theorem resolve1 {a b : Bool} (H1 : a ∨ b) (H2 : ¬ a) : b
:= H1 H2

-- Recall that and is defined as ¬ (a → ¬ b)
theorem and_intro {a b : Bool} (H1 : a) (H2 : b) : a ∧ b
:= λ H : a → ¬ b, absurd H2 (H H1)

theorem and_eliml {a b : Bool} (H : a ∧ b) : a
:= not_imp_eliml H

theorem and_elimr {a b : Bool} (H : a ∧ b) : b
:= not_not_elim (not_imp_elimr H)

-- Recall that or is defined as ¬ a → b
theorem or_introl {a : Bool} (H : a) (b : Bool) : a ∨ b
:= λ H1 : ¬ a, absurd_elim b H H1

theorem or_intror {b : Bool} (a : Bool) (H : b) : a ∨ b
:= λ H1 : ¬ a, H

theorem or_elim {a b c : Bool} (H1 : a ∨ b) (H2 : a → c) (H3 : b → c) : c
:= not_not_elim
     (λ H : ¬ c,
        absurd (have c : H3 (have b : resolve1 H1 (have ¬ a : (mt (λ Ha : a, H2 Ha) H))))
               H)

theorem refute {a : Bool} (H : ¬ a → false) : a
:= or_elim (em a) (λ H1 : a, H1) (λ H1 : ¬ a, false_elim a (H H1))

theorem symm {A : TypeU} {a b : A} (H : a == b) : b == a
:= subst (refl a) H

theorem trans {A : TypeU} {a b c : A} (H1 : a == b) (H2 : b == c) : a == c
:= subst H1 H2

infixl 100 ⋈ : trans

theorem ne_symm {A : TypeU} {a b : A} (H : a ≠ b) : b ≠ a
:= λ H1 : b = a, H (symm H1)

theorem eq_ne_trans {A : TypeU} {a b c : A} (H1 : a = b) (H2 : b ≠ c) : a ≠ c
:= subst H2 (symm H1)

theorem ne_eq_trans {A : TypeU} {a b c : A} (H1 : a ≠ b) (H2 : b = c) : a ≠ c
:= subst H1 H2

theorem eqt_elim {a : Bool} (H : a == true) : a
:= (symm H) ◂ trivial

theorem congr1 {A : TypeU} {B : A → TypeU} {f g : ∀ x : A, B x} (a : A) (H : f == g) : f a == g a
:= substp (fun h : (∀ x : A, B x), f a == h a) (refl (f a)) H

theorem congr2 {A : TypeU} {B : A → TypeU} {a b : A} (f : ∀ x : A, B x) (H : a == b) : f a == f b
:= substp (fun x : A, f a == f x) (refl (f a)) H

theorem congr {A : TypeU} {B : A → TypeU} {f g : ∀ x : A, B x} {a b : A} (H1 : f == g) (H2 : a == b) : f a == g b
:= subst (congr2 f H2) (congr1 b H1)

-- Recall that exists is defined as ¬ ∀ x : A, ¬ P x
theorem exists_elim {A : TypeU} {P : A → Bool} {B : Bool} (H1 : Exists A P) (H2 : ∀ (a : A) (H : P a), B) : B
:= refute (λ R : ¬ B,
             absurd (λ a : A, mt (λ H : P a, H2 a H) R)
                    H1)

theorem exists_intro {A : TypeU} {P : A → Bool} (a : A) (H : P a) : Exists A P
:= λ H1 : (∀ x : A, ¬ P x),
      absurd H (H1 a)

theorem boolext {a b : Bool} (Hab : a → b) (Hba : b → a) : a == b
:= or_elim (boolcomplete a)
       (λ Hat : a == true,  or_elim (boolcomplete b)
           (λ Hbt : b == true,  trans Hat (symm Hbt))
           (λ Hbf : b == false, false_elim (a == b) (subst (Hab (eqt_elim Hat)) Hbf)))
       (λ Haf : a == false, or_elim (boolcomplete b)
           (λ Hbt : b == true,  false_elim (a == b) (subst (Hba (eqt_elim Hbt)) Haf))
           (λ Hbf : b == false, trans Haf (symm Hbf)))

theorem iff_intro {a b : Bool} (Hab : a → b) (Hba : b → a) : a == b
:= boolext Hab Hba

theorem eqt_intro {a : Bool} (H : a) : a == true
:= boolext (λ H1 : a, trivial)
           (λ H2 : true, H)

theorem or_comm (a b : Bool) : (a ∨ b) == (b ∨ a)
:= boolext (λ H, or_elim H (λ H1, or_intror b H1) (λ H2, or_introl H2 a))
           (λ H, or_elim H (λ H1, or_intror a H1) (λ H2, or_introl H2 b))

theorem or_assoc (a b c : Bool) : ((a ∨ b) ∨ c) == (a ∨ (b ∨ c))
:= boolext (λ H : (a ∨ b) ∨ c,
                      or_elim H (λ H1 : a ∨ b, or_elim H1 (λ Ha : a, or_introl Ha (b ∨ c))
                                                          (λ Hb : b, or_intror a (or_introl Hb c)))
                                (λ Hc : c, or_intror a (or_intror b Hc)))
           (λ H : a ∨ (b ∨ c),
                      or_elim H (λ Ha : a, (or_introl (or_introl Ha b) c))
                                (λ H1 : b ∨ c, or_elim H1 (λ Hb : b, or_introl (or_intror a Hb) c)
                                                          (λ Hc : c, or_intror (a ∨ b) Hc)))

theorem or_id (a : Bool) : (a ∨ a) == a
:= boolext (λ H, or_elim H (λ H1, H1) (λ H2, H2))
           (λ H, or_introl H a)

theorem or_falsel (a : Bool) : (a ∨ false) == a
:= boolext (λ H, or_elim H (λ H1, H1) (λ H2, false_elim a H2))
           (λ H, or_introl H false)

theorem or_falser (a : Bool) : (false ∨ a) == a
:= (or_comm false a) ⋈ (or_falsel a)

theorem or_truel (a : Bool) : (true ∨ a) == true
:= eqt_intro (case (λ x : Bool, true ∨ x) trivial trivial a)

theorem or_truer (a : Bool) : (a ∨ true) == true
:= (or_comm a true) ⋈ (or_truel a)

theorem or_tauto (a : Bool) : (a ∨ ¬ a) == true
:= eqt_intro (em a)

theorem and_comm (a b : Bool) : (a ∧ b) == (b ∧ a)
:= boolext (λ H, and_intro (and_elimr H) (and_eliml H))
           (λ H, and_intro (and_elimr H) (and_eliml H))

theorem and_id (a : Bool) : (a ∧ a) == a
:= boolext (λ H, and_eliml H)
           (λ H, and_intro H H)

theorem and_assoc (a b c : Bool) : ((a ∧ b) ∧ c) == (a ∧ (b ∧ c))
:= boolext (λ H, and_intro (and_eliml (and_eliml H)) (and_intro (and_elimr (and_eliml H)) (and_elimr H)))
           (λ H, and_intro (and_intro (and_eliml H) (and_eliml (and_elimr H))) (and_elimr (and_elimr H)))

theorem and_truer (a : Bool) : (a ∧ true) == a
:= boolext (λ H : a ∧ true,  and_eliml H)
           (λ H : a,         and_intro H trivial)

theorem and_truel (a : Bool) : (true ∧ a) == a
:= trans (and_comm true a) (and_truer a)

theorem and_falsel (a : Bool) : (a ∧ false) == false
:= boolext (λ H, and_elimr H)
           (λ H, false_elim (a ∧ false) H)

theorem and_falser (a : Bool) : (false ∧ a) == false
:= (and_comm false a) ⋈ (and_falsel a)

theorem and_absurd (a : Bool) : (a ∧ ¬ a) == false
:= boolext (λ H, absurd (and_eliml H) (and_elimr H))
           (λ H, false_elim (a ∧ ¬ a) H)

theorem not_true : (¬ true) == false
:= trivial

theorem not_false : (¬ false) == true
:= trivial

theorem not_and (a b : Bool) : (¬ (a ∧ b)) == (¬ a ∨ ¬ b)
:= case (λ x, (¬ (x ∧ b)) == (¬ x ∨ ¬ b))
        (case (λ y, (¬ (true ∧ y)) == (¬ true ∨ ¬ y))   trivial trivial b)
        (case (λ y, (¬ (false ∧ y)) == (¬ false ∨ ¬ y)) trivial trivial b)
        a

theorem not_and_elim {a b : Bool} (H : ¬ (a ∧ b)) : ¬ a ∨ ¬ b
:= (not_and a b) ◂ H

theorem not_or (a b : Bool) : (¬ (a ∨ b)) == (¬ a ∧ ¬ b)
:= case (λ x, (¬ (x ∨ b)) == (¬ x ∧ ¬ b))
        (case (λ y, (¬ (true ∨ y)) == (¬ true ∧ ¬ y))   trivial trivial b)
        (case (λ y, (¬ (false ∨ y)) == (¬ false ∧ ¬ y)) trivial trivial b)
        a

theorem not_or_elim {a b : Bool} (H : ¬ (a ∨ b)) : ¬ a ∧ ¬ b
:= (not_or a b) ◂ H

theorem not_iff (a b : Bool) : (¬ (a == b)) == ((¬ a) == b)
:= case (λ x, (¬ (x == b)) == ((¬ x) == b))
        (case (λ y, (¬ (true == y)) == ((¬ true) == y)) trivial trivial b)
        (case (λ y, (¬ (false == y)) == ((¬ false) == y)) trivial trivial b)
        a

theorem not_iff_elim {a b : Bool} (H : ¬ (a == b)) : (¬ a) == b
:= (not_iff a b) ◂ H

theorem not_implies (a b : Bool) : (¬ (a → b)) == (a ∧ ¬ b)
:= case (λ x, (¬ (x → b)) == (x ∧ ¬ b))
        (case (λ y, (¬ (true → y)) == (true ∧ ¬ y)) trivial trivial b)
        (case (λ y, (¬ (false → y)) == (false ∧ ¬ y)) trivial trivial b)
        a

theorem not_implies_elim {a b : Bool} (H : ¬ (a → b)) : a ∧ ¬ b
:= (not_implies a b) ◂ H

theorem not_congr {a b : Bool} (H : a == b) : (¬ a) == (¬ b)
:= congr2 not H

theorem eq_exists_intro {A : (Type U)} {P Q : A → Bool} (H : ∀ x : A, P x == Q x) : (∃ x : A, P x) == (∃ x : A, Q x)
:= congr2 (Exists A) (funext H)

theorem not_forall (A : (Type U)) (P : A → Bool) : (¬ (∀ x : A, P x)) == (∃ x : A, ¬ P x)
:= calc (¬ ∀ x : A, P x) = (¬ ∀ x : A, ¬ ¬ P x) : not_congr (allext (λ x : A, symm (not_not_eq (P x))))
              ...        = (∃ x : A, ¬ P x)     : refl (∃ x : A, ¬ P x)

theorem not_forall_elim {A : (Type U)} {P : A → Bool} (H : ¬ (∀ x : A, P x)) : ∃ x : A, ¬ P x
:= (not_forall A P) ◂ H

theorem not_exists (A : (Type U)) (P : A → Bool) : (¬ ∃ x : A, P x) == (∀ x : A, ¬ P x)
:= calc (¬ ∃ x : A, P x) = (¬ ¬ ∀ x : A, ¬ P x) : refl (¬ ∃ x : A, P x)
                     ... = (∀ x : A, ¬ P x)     : not_not_eq (∀ x : A, ¬ P x)

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

theorem exists_unfold {A : TypeU} (P : A → Bool) (a : A) : (∃ x : A, P x) = (P a ∨ (∃ x : A, x ≠ a ∧ P x))
:= boolext (λ H : (∃ x : A, P x), exists_unfold1 a H)
           (λ H : (P a ∨ (∃ x : A, x ≠ a ∧ P x)), exists_unfold2 a H)

set_opaque exists  true
set_opaque not     true
set_opaque or      true
set_opaque and     true
set_opaque implies true