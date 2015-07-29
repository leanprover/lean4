/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.datatypes init.reserved_notation

/- implication -/

definition implies (a b : Prop) := a → b

lemma implies.trans [trans] {p q r : Prop} (h₁ : implies p q) (h₂ : implies q r) : implies p r :=
assume hp, h₂ (h₁ hp)

definition trivial := true.intro

definition not (a : Prop) := a → false
prefix `¬` := not

definition absurd {a : Prop} {b : Type} (H1 : a) (H2 : ¬a) : b :=
false.rec b (H2 H1)

/- not -/

theorem not_false : ¬false :=
assume H : false, H

definition non_contradictory (a : Prop) : Prop := ¬¬a

theorem non_contradictory_intro {a : Prop} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

/- eq -/

notation a = b := eq a b
definition rfl {A : Type} {a : A} : a = a := eq.refl a

-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (H₁ H₂ : a) : H₁ = H₂ :=
rfl

-- Remark: we provide the universe levels explicitly to make sure `eq.drec` has the same type of `eq.rec` in the HoTT library
protected theorem eq.drec.{l₁ l₂} {A : Type.{l₂}} {a : A} {C : Π (x : A), a = x → Type.{l₁}} (h₁ : C a (eq.refl a)) {b : A} (h₂ : a = b) : C b h₂ :=
eq.rec (λh₂ : a = a, show C a h₂, from h₁) h₂ h₂

namespace eq
  variables {A : Type}
  variables {a b c a': A}

  protected theorem drec_on {a : A} {C : Π (x : A), a = x → Type} {b : A} (h₂ : a = b) (h₁ : C a (refl a)) : C b h₂ :=
  eq.drec h₁ h₂

  theorem subst {P : A → Prop} (H₁ : a = b) (H₂ : P a) : P b :=
  eq.rec H₂ H₁

  theorem trans (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  theorem symm : a = b → b = a :=
  eq.rec (refl a)

  theorem substr {P : A → Prop} (H₁ : b = a) : P a → P b :=
  subst (symm H₁)

  namespace ops
    notation H `⁻¹` := symm H --input with \sy or \-1 or \inv
    notation H1 ⬝ H2 := trans H1 H2
    notation H1 ▸ H2 := subst H1 H2
    notation H1 ▹ H2 := eq.rec H2 H1
  end ops
end eq

theorem congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
eq.subst H₁ (eq.subst H₂ rfl)

theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
eq.subst H (eq.refl (f a))

theorem congr_arg {A B : Type} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂ :=
congr rfl

section
  variables {A : Type} {a b c: A}
  open eq.ops

  theorem trans_rel_left (R : A → A → Prop) (H₁ : R a b) (H₂ : b = c) : R a c :=
  H₂ ▸ H₁

  theorem trans_rel_right (R : A → A → Prop) (H₁ : a = b) (H₂ : R b c) : R a c :=
  H₁⁻¹ ▸ H₂
end

section
  variable {p : Prop}
  open eq.ops

  theorem of_eq_true (H : p = true) : p :=
  H⁻¹ ▸ trivial

  theorem not_of_eq_false (H : p = false) : ¬p :=
  assume Hp, H ▸ Hp
end

attribute eq.subst [subst]
attribute eq.refl [refl]
attribute eq.trans [trans]
attribute eq.symm [symm]

/- ne -/

definition ne {A : Type} (a b : A) := ¬(a = b)
notation a ≠ b := ne a b

namespace ne
  open eq.ops
  variable {A : Type}
  variables {a b : A}

  theorem intro (H : a = b → false) : a ≠ b := H

  theorem elim (H : a ≠ b) : a = b → false := H

  theorem irrefl (H : a ≠ a) : false := H rfl

  theorem symm (H : a ≠ b) : b ≠ a :=
  assume (H₁ : b = a), H (H₁⁻¹)
end ne

theorem false.of_ne {A : Type} {a : A} : a ≠ a → false := ne.irrefl

infixl `==`:50 := heq

namespace heq
  universe variable u
  variables {A B C : Type.{u}} {a a' : A} {b b' : B} {c : C}

  theorem to_eq (H : a == a') : a = a' :=
  have H₁ : ∀ (Ht : A = A), eq.rec a Ht = a, from
    λ Ht, eq.refl a,
  heq.rec H₁ H (eq.refl A)

  theorem elim {A : Type} {a : A} {P : A → Type} {b : A} (H₁ : a == b)
    : P a → P b := eq.rec_on (to_eq H₁)

  theorem subst {P : ∀T : Type, T → Prop} : a == b → P A a → P B b :=
  heq.rec_on

  theorem symm (H : a == b) : b == a :=
  heq.rec_on H (refl a)

  theorem of_eq (H : a = a') : a == a' :=
  eq.subst H (refl a)

  theorem trans (H₁ : a == b) (H₂ : b == c) : a == c :=
  subst H₂ H₁

  theorem of_heq_of_eq (H₁ : a == b) (H₂ : b = b') : a == b' :=
  trans H₁ (of_eq H₂)

  theorem of_eq_of_heq (H₁ : a = a') (H₂ : a' == b) : a == b :=
  trans (of_eq H₁) H₂

  definition type_eq (H : a == b) : A = B :=
  heq.rec_on H (eq.refl A)
end heq

open eq.ops
theorem eq_rec_heq {A : Type} {P : A → Type} {a a' : A} (H : a = a') (p : P a) : H ▹ p == p :=
eq.drec_on H !heq.refl

theorem eq_rec_of_heq_left : ∀ {A₁ A₂ : Type} {a₁ : A₁} {a₂ : A₂} (h : a₁ == a₂), heq.type_eq h ▹ a₁ = a₂
| A A a a (heq.refl a) := rfl

reveal eq.symm
theorem eq_rec_of_heq_right : ∀ {A₁ A₂ : Type} {a₁ : A₁} {a₂ : A₂} (h : a₁ == a₂), a₁ = (heq.type_eq h)⁻¹ ▹ a₂
| A A a a (heq.refl a) := rfl

theorem heq_of_eq_rec_left {A : Type} {P : A → Type} : ∀ {a a' : A} {p₁ : P a} {p₂ : P a'} (e : a = a') (h₂ : e ▹ p₁ = p₂), p₁ == p₂
| a a p₁ p₂ (eq.refl a) h := eq.rec_on h !heq.refl

theorem heq_of_eq_rec_right {A : Type} {P : A → Type} : ∀ {a a' : A} {p₁ : P a} {p₂ : P a'} (e : a' = a) (h₂ : p₁ = e ▹ p₂), p₁ == p₂
| a a p₁ p₂ (eq.refl a) h := eq.rec_on h !heq.refl

theorem of_heq_true {a : Prop} (H : a == true) : a :=
of_eq_true (heq.to_eq H)

theorem eq_rec_compose : ∀ {A B C : Type} (p₁ : B = C) (p₂ : A = B) (a : A), p₁ ▹ (p₂ ▹ a : B) = (p₂ ⬝ p₁) ▹ a
| A A A (eq.refl A) (eq.refl A) a := calc
  eq.refl A ▹ eq.refl A ▹ a = eq.refl A ▹ a              : rfl
            ...             = (eq.refl A ⬝ eq.refl A) ▹ a : {proof_irrel (eq.refl A) (eq.refl A ⬝ eq.refl A)}

attribute heq.refl [refl]
attribute heq.trans [trans]
attribute heq.of_heq_of_eq [trans]
attribute heq.of_eq_of_heq [trans]
attribute heq.symm [symm]

/- and -/

notation a /\ b := and a b
notation a ∧ b  := and a b

variables {a b c d : Prop}

theorem and.elim (H₁ : a ∧ b) (H₂ : a → b → c) : c :=
and.rec H₂ H₁

/- or -/

notation a `\/` b := or a b
notation a ∨ b := or a b

namespace or
  theorem elim (H₁ : a ∨ b) (H₂ : a → c) (H₃ : b → c) : c :=
  or.rec H₂ H₃ H₁
end or

theorem non_contradictory_em (a : Prop) : ¬¬(a ∨ ¬a) :=
assume not_em : ¬(a ∨ ¬a),
  have neg_a : ¬a, from
    assume pos_a : a, absurd (or.inl pos_a) not_em,
  absurd (or.inr neg_a) not_em

/- iff -/

definition iff (a b : Prop) := (a → b) ∧ (b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

namespace iff
  theorem intro : (a → b) → (b → a) → (a ↔ b) := and.intro

  theorem elim : ((a → b) → (b → a) → c) → (a ↔ b) → c := and.rec

  theorem elim_left : (a ↔ b) → a → b := and.left

  definition mp := @elim_left

  theorem elim_right : (a ↔ b) → b → a := and.right

  definition mpr := @elim_right

  theorem refl (a : Prop) : a ↔ a :=
  intro (assume H, H) (assume H, H)

  theorem rfl {a : Prop} : a ↔ a :=
  refl a

  theorem trans (H₁ : a ↔ b) (H₂ : b ↔ c) : a ↔ c :=
  intro
    (assume Ha, mp H₂ (mp H₁ Ha))
    (assume Hc, mpr H₁ (mpr H₂ Hc))

  theorem symm (H : a ↔ b) : b ↔ a :=
  intro (elim_right H) (elim_left H)

  theorem comm : (a ↔ b) ↔ (b ↔ a) :=
  intro symm symm

  open eq.ops
  theorem of_eq {a b : Prop} (H : a = b) : a ↔ b :=
  H ▸ rfl
end iff

theorem not_iff_not_of_iff (H₁ : a ↔ b) : ¬a ↔ ¬b :=
iff.intro
 (assume (Hna : ¬ a) (Hb : b), Hna (iff.elim_right H₁ Hb))
 (assume (Hnb : ¬ b) (Ha : a), Hnb (iff.elim_left H₁ Ha))

theorem of_iff_true (H : a ↔ true) : a :=
iff.mp (iff.symm H) trivial

theorem not_of_iff_false : (a ↔ false) → ¬a := iff.mp

theorem iff_true_intro (H : a) : a ↔ true :=
iff.intro
  (λ Hl, trivial)
  (λ Hr, H)

theorem iff_false_intro (H : ¬a) : a ↔ false :=
iff.intro H !false.rec

theorem not_non_contradictory_iff_absurd (a : Prop) : ¬¬¬a ↔ ¬a :=
iff.intro
  (λ (Hl : ¬¬¬a) (Ha : a), Hl (non_contradictory_intro Ha))
  absurd

attribute iff.refl [refl]
attribute iff.symm [symm]
attribute iff.trans [trans]

inductive Exists {A : Type} (P : A → Prop) : Prop :=
intro : ∀ (a : A), P a → Exists P

definition exists.intro := @Exists.intro

notation `exists` binders `,` r:(scoped P, Exists P) := r
notation `∃` binders `,` r:(scoped P, Exists P) := r

theorem exists.elim {A : Type} {p : A → Prop} {B : Prop}
  (H1 : ∃x, p x) (H2 : ∀ (a : A), p a → B) : B :=
Exists.rec H2 H1

/- decidable -/

inductive decidable [class] (p : Prop) : Type :=
| inl :  p → decidable p
| inr : ¬p → decidable p

definition decidable_true [instance] : decidable true :=
decidable.inl trivial

definition decidable_false [instance] : decidable false :=
decidable.inr not_false

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
definition dite (c : Prop) [H : decidable c] {A : Type} : (c → A) → (¬ c → A) → A :=
decidable.rec_on H

/- if-then-else -/

definition ite (c : Prop) [H : decidable c] {A : Type} (t e : A) : A :=
decidable.rec_on H (λ Hc, t) (λ Hnc, e)

namespace decidable
  variables {p q : Prop}

  definition rec_on_true [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : p) (H4 : H1 H3)
      : decidable.rec_on H H1 H2 :=
  decidable.rec_on H (λh, H4) (λh, !false.rec (h H3))

  definition rec_on_false [H : decidable p] {H1 : p → Type} {H2 : ¬p → Type} (H3 : ¬p) (H4 : H2 H3)
      : decidable.rec_on H H1 H2 :=
  decidable.rec_on H (λh, false.rec _ (H3 h)) (λh, H4)

  definition by_cases {q : Type} [C : decidable p] : (p → q) → (¬p → q) → q := !dite

  theorem em (p : Prop) [H : decidable p] : p ∨ ¬p := by_cases or.inl or.inr

  theorem by_contradiction [Hp : decidable p] (H : ¬p → false) : p :=
  if H1 : p then H1 else false.rec _ (H H1)
end decidable

section
  variables {p q : Prop}
  open decidable
  definition  decidable_of_decidable_of_iff (Hp : decidable p) (H : p ↔ q) : decidable q :=
  if Hp : p then inl (iff.mp H Hp)
  else inr (iff.mp (not_iff_not_of_iff H) Hp)

  definition  decidable_of_decidable_of_eq (Hp : decidable p) (H : p = q) : decidable q :=
  decidable_of_decidable_of_iff Hp (iff.of_eq H)

  protected definition or.by_cases [Hp : decidable p] [Hq : decidable q] {A : Type}
                                   (h : p ∨ q) (h₁ : p → A) (h₂ : q → A) : A :=
  if hp : p then h₁ hp else
    if hq : q then h₂ hq else
      false.rec _ (or.elim h hp hq)
end

section
  variables {p q : Prop}
  open decidable (rec_on inl inr)

  definition decidable_and [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ∧ q) :=
  if hp : p then
    if hq : q then inl (and.intro hp hq)
    else inr (assume H : p ∧ q, hq (and.right H))
  else inr (assume H : p ∧ q, hp (and.left H))

  definition decidable_or [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ∨ q) :=
  if hp : p then inl (or.inl hp) else
    if hq : q then inl (or.inr hq) else
      inr (or.rec hp hq)

  definition decidable_not [instance] [Hp : decidable p] : decidable (¬p) :=
  if hp : p then inr (absurd hp) else inl hp

  definition decidable_implies [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p → q) :=
  if hp : p then
    if hq : q then inl (assume H, hq)
    else inr (assume H : p → q, absurd (H hp) hq)
  else inl (assume Hp, absurd Hp hp)

  definition decidable_iff [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ↔ q) :=
  decidable_and

end

definition decidable_pred [reducible] {A : Type} (R : A   →   Prop) := Π (a   : A), decidable (R a)
definition decidable_rel  [reducible] {A : Type} (R : A → A → Prop) := Π (a b : A), decidable (R a b)
definition decidable_eq   [reducible] (A : Type) := decidable_rel (@eq A)
definition decidable_ne [instance] {A : Type} [H : decidable_eq A] (a b : A) : decidable (a ≠ b) :=
decidable_implies

namespace bool
  theorem ff_ne_tt : ff = tt → false
  | [none]
end bool

open bool
definition is_dec_eq {A : Type} (p : A → A → bool) : Prop   := ∀ ⦃x y : A⦄, p x y = tt → x = y
definition is_dec_refl {A : Type} (p : A → A → bool) : Prop := ∀x, p x x = tt

open decidable
protected definition bool.has_decidable_eq [instance] : ∀a b : bool, decidable (a = b)
| ff ff := inl rfl
| ff tt := inr ff_ne_tt
| tt ff := inr (ne.symm ff_ne_tt)
| tt tt := inl rfl

definition decidable_eq_of_bool_pred {A : Type} {p : A → A → bool} (H₁ : is_dec_eq p) (H₂ : is_dec_refl p) : decidable_eq A :=
take x y : A, if Hp : p x y = tt then inl (H₁ Hp)
 else inr (assume Hxy : x = y, (eq.subst Hxy Hp) (H₂ y))

theorem decidable_eq_inl_refl {A : Type} [H : decidable_eq A] (a : A) : H a a = inl (eq.refl a) :=
match H a a with
| inl e := rfl
| inr n := absurd rfl n
end

open eq.ops
theorem decidable_eq_inr_neg {A : Type} [H : decidable_eq A] {a b : A} : Π n : a ≠ b, H a b = inr n :=
assume n,
match H a b with
| inl e  := absurd e n
| inr n₁ := proof_irrel n n₁ ▸ rfl
end

/- inhabited -/

inductive inhabited [class] (A : Type) : Type :=
mk : A → inhabited A

protected definition inhabited.value {A : Type} : inhabited A → A :=
inhabited.rec (λa, a)

protected definition inhabited.destruct {A : Type} {B : Type} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited.rec H2 H1

definition default (A : Type) [H : inhabited A] : A :=
inhabited.value H

definition arbitrary [irreducible] (A : Type) [H : inhabited A] : A :=
inhabited.value H

definition Prop.is_inhabited [instance] : inhabited Prop :=
inhabited.mk true

definition inhabited_fun [instance] (A : Type) {B : Type} [H : inhabited B] : inhabited (A → B) :=
inhabited.rec_on H (λb, inhabited.mk (λa, b))

definition inhabited_Pi [instance] (A : Type) {B : A → Type} [H : Πx, inhabited (B x)] :
  inhabited (Πx, B x) :=
inhabited.mk (λa, !default)

protected definition bool.is_inhabited [instance] : inhabited bool :=
inhabited.mk ff

inductive nonempty [class] (A : Type) : Prop :=
intro : A → nonempty A

protected definition nonempty.elim {A : Type} {B : Prop} (H1 : nonempty A) (H2 : A → B) : B :=
nonempty.rec H2 H1

theorem nonempty_of_inhabited [instance] {A : Type} [H : inhabited A] : nonempty A :=
nonempty.intro !default

/- subsingleton -/

inductive subsingleton [class] (A : Type) : Prop :=
intro : (∀ a b : A, a = b) → subsingleton A

protected definition subsingleton.elim {A : Type} [H : subsingleton A] : ∀(a b : A), a = b :=
subsingleton.rec (λp, p) H

definition subsingleton_prop [instance] (p : Prop) : subsingleton p :=
subsingleton.intro (λa b, !proof_irrel)

definition subsingleton_decidable [instance] (p : Prop) : subsingleton (decidable p) :=
subsingleton.intro (λ d₁,
  match d₁ with
  | inl t₁ := (λ d₂,
    match d₂ with
    | inl t₂ := eq.rec_on (proof_irrel t₁ t₂) rfl
    | inr f₂ := absurd t₁ f₂
    end)
  | inr f₁ := (λ d₂,
    match d₂ with
    | inl t₂ := absurd t₂ f₁
    | inr f₂ := eq.rec_on (proof_irrel f₁ f₂) rfl
    end)
  end)

protected theorem rec_subsingleton {p : Prop} [H : decidable p]
    {H1 : p → Type} {H2 : ¬p → Type}
    [H3 : Π(h : p), subsingleton (H1 h)] [H4 : Π(h : ¬p), subsingleton (H2 h)]
  : subsingleton (decidable.rec_on H H1 H2) :=
decidable.rec_on H (λh, H3 h) (λh, H4 h) --this can be proven using dependent version of "by_cases"

theorem if_pos {c : Prop} [H : decidable c] (Hc : c) {A : Type} {t e : A} : (ite c t e) = t :=
decidable.rec
  (λ Hc : c,    eq.refl (@ite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

theorem if_neg {c : Prop} [H : decidable c] (Hnc : ¬c) {A : Type} {t e : A} : (ite c t e) = e :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@ite c (decidable.inr Hnc) A t e))
  H

theorem if_t_t [simp] (c : Prop) [H : decidable c] {A : Type} (t : A) : (ite c t t) = t :=
decidable.rec
  (λ Hc  : c,  eq.refl (@ite c (decidable.inl Hc)  A t t))
  (λ Hnc : ¬c, eq.refl (@ite c (decidable.inr Hnc) A t t))
  H

theorem implies_of_if_pos {c t e : Prop} [H : decidable c] (h : ite c t e) : c → t :=
assume Hc, eq.rec_on (if_pos Hc) h

theorem implies_of_if_neg {c t e : Prop} [H : decidable c] (h : ite c t e) : ¬c → e :=
assume Hnc, eq.rec_on (if_neg Hnc) h

theorem if_ctx_congr {A : Type} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                     {x y u v : A}
                     (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = ite c u v :=
decidable.rec_on dec_b
  (λ hp : b, calc
    ite b x y = x           : if_pos hp
         ...  = u           : h_t (iff.mp h_c hp)
         ...  = ite c u v : if_pos (iff.mp h_c hp))
  (λ hn : ¬b, calc
    ite b x y = y         : if_neg hn
         ...  = v         : h_e (iff.mp (not_iff_not_of_iff h_c) hn)
         ...  = ite c u v : if_neg (iff.mp (not_iff_not_of_iff h_c) hn))

theorem if_congr {A : Type} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                 {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr A b c dec_b dec_c x y u v h_c (λ h, h_t) (λ h, h_e)

theorem if_ctx_simp_congr {A : Type} {b c : Prop} [dec_b : decidable b] {x y u v : A}
                        (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x y u v h_c h_t h_e

theorem if_simp_congr [congr] {A : Type} {b c : Prop} [dec_b : decidable b] {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_simp_congr A b c dec_b x y u v h_c (λ h, h_t) (λ h, h_e)

theorem if_congr_prop {b c x y u v : Prop} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ ite c u v :=
decidable.rec_on dec_b
  (λ hp : b, calc
    ite b x y ↔ x         : iff.of_eq (if_pos hp)
         ...  ↔ u         : h_t (iff.mp h_c hp)
         ...  ↔ ite c u v : iff.of_eq (if_pos (iff.mp h_c hp)))
  (λ hn : ¬b, calc
    ite b x y ↔ y         : iff.of_eq (if_neg hn)
         ...  ↔ v         : h_e (iff.mp (not_iff_not_of_iff h_c) hn)
         ...  ↔ ite c u v : iff.of_eq (if_neg (iff.mp (not_iff_not_of_iff h_c) hn)))

theorem if_ctx_simp_congr_prop {b c x y u v : Prop} [dec_b : decidable b]
                               (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Prop u v) :=
@if_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff dec_b h_c) h_c h_t h_e

theorem if_simp_congr_prop [congr] {b c x y u v : Prop} [dec_b : decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Prop u v) :=
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (λ h, h_t) (λ h, h_e)

theorem dif_pos {c : Prop} [H : decidable c] (Hc : c) {A : Type} {t : c → A} {e : ¬ c → A} : dite c t e = t Hc :=
decidable.rec
  (λ Hc : c,    eq.refl (@dite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

theorem dif_neg {c : Prop} [H : decidable c] (Hnc : ¬c) {A : Type} {t : c → A} {e : ¬ c → A} : dite c t e = e Hnc :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@dite c (decidable.inr Hnc) A t e))
  H

theorem dif_ctx_congr {A : Type} {b c : Prop} [dec_b : decidable b] [dec_c : decidable c]
                      {x : b → A} {u : c → A} {y : ¬b → A} {v : ¬c → A}
                      (h_c : b ↔ c)
                      (h_t : ∀ (h : c),    x (iff.mpr h_c h)                      = u h)
                      (h_e : ∀ (h : ¬c),   y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b A x y) = (@dite c dec_c A u v) :=
decidable.rec_on dec_b
  (λ hp : b, calc
    dite b x y = x hp                            : dif_pos hp
          ...  = x (iff.mpr h_c (iff.mp h_c hp)) : proof_irrel
          ...  = u (iff.mp h_c hp)               : h_t
          ...  = dite c u v                      : dif_pos (iff.mp h_c hp))
  (λ hn : ¬b, let h_nc : ¬b ↔ ¬c := not_iff_not_of_iff h_c in calc
    dite b x y = y hn                              : dif_neg hn
          ...  = y (iff.mpr h_nc (iff.mp h_nc hn)) : proof_irrel
          ...  = v (iff.mp h_nc hn)                : h_e
          ...  = dite c u v                        : dif_neg (iff.mp h_nc hn))

theorem dif_ctx_simp_congr {A : Type} {b c : Prop} [dec_b : decidable b]
                         {x : b → A} {u : c → A} {y : ¬b → A} {v : ¬c → A}
                         (h_c : b ↔ c)
                         (h_t : ∀ (h : c),    x (iff.mpr h_c h)                      = u h)
                         (h_e : ∀ (h : ¬c),   y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b A x y) = (@dite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@dif_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x u y v h_c h_t h_e

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
theorem dite_ite_eq (c : Prop) [H : decidable c] {A : Type} (t : A) (e : A) : dite c (λh, t) (λh, e) = ite c t e :=
rfl

definition is_true (c : Prop) [H : decidable c] : Prop :=
if c then true else false

definition is_false (c : Prop) [H : decidable c] : Prop :=
if c then false else true

theorem of_is_true {c : Prop} [H₁ : decidable c] (H₂ : is_true c) : c :=
decidable.rec_on H₁ (λ Hc, Hc) (λ Hnc, !false.rec (if_neg Hnc ▸ H₂))

notation `dec_trivial` := of_is_true trivial

theorem not_of_not_is_true {c : Prop} [H₁ : decidable c] (H₂ : ¬ is_true c) : ¬ c :=
if Hc : c then absurd trivial (if_pos Hc ▸ H₂) else Hc

theorem not_of_is_false {c : Prop} [H₁ : decidable c] (H₂ : is_false c) : ¬ c :=
if Hc : c then !false.rec (if_pos Hc ▸ H₂) else Hc

theorem of_not_is_false {c : Prop} [H₁ : decidable c] (H₂ : ¬ is_false c) : c :=
if Hc : c then Hc else absurd trivial (if_neg Hc ▸ H₂)

-- namespace used to collect congruence rules for "contextual simplification"
namespace contextual
  attribute if_ctx_simp_congr      [congr]
  attribute if_ctx_simp_congr_prop [congr]
  attribute dif_ctx_simp_congr     [congr]
end contextual
