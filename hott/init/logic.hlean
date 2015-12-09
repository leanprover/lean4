/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Floris van Doorn
-/

prelude
import init.reserved_notation
open unit

definition id [reducible] [unfold_full] {A : Type} (a : A) : A :=
a

/- not -/

definition not [reducible] (a : Type) := a → empty
prefix ¬ := not

definition absurd {a b : Type} (H₁ : a) (H₂ : ¬a) : b :=
empty.rec (λ e, b) (H₂ H₁)

definition mt {a b : Type} (H₁ : a → b) (H₂ : ¬b) : ¬a :=
assume Ha : a, absurd (H₁ Ha) H₂

definition not_empty : ¬empty :=
assume H : empty, H

definition non_contradictory (a : Type) : Type := ¬¬a

definition non_contradictory_intro {a : Type} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

definition not.intro {a : Type} (H : a → empty) : ¬a := H

/- empty -/

definition empty.elim {c : Type} (H : empty) : c :=
empty.rec _ H

/- eq -/

infix = := eq
definition rfl {A : Type} {a : A} := eq.refl a

/-
  These notions are here only to make porting from the standard library easier.
  They are defined again in init/path.hlean, and those definitions will be used
  throughout the HoTT-library. That's why the notation for eq below is only local.
-/
namespace eq
  variables {A : Type} {a b c : A}

  definition subst [unfold 5] {P : A → Type} (H₁ : a = b) (H₂ : P a) : P b :=
  eq.rec H₂ H₁

  definition trans [unfold 5] (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  definition symm [unfold 4] (H : a = b) : b = a :=
  subst H (refl a)

  definition mp {a b : Type} : (a = b) → a → b :=
  eq.rec_on

  definition mpr {a b : Type} : (a = b) → b → a :=
  assume H₁ H₂, eq.rec_on (eq.symm H₁) H₂

  namespace ops end ops -- this is just to ensure that this namespace exists. There is nothing in it
end eq

local postfix ⁻¹ := eq.symm --input with \sy or \-1 or \inv
local infixl ⬝ := eq.trans
local infixr ▸ := eq.subst

-- Auxiliary definition used by automation. It has the same type of eq.rec in the standard library
definition eq.nrec.{l₁ l₂} {A : Type.{l₂}} {a : A} {C : A → Type.{l₁}} (H₁ : C a) (b : A) (H₂ : a = b) : C b :=
eq.rec H₁ H₂

definition congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
eq.subst H₁ (eq.subst H₂ rfl)

definition congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
eq.subst H (eq.refl (f a))

definition congr_arg {A B : Type} (a a' : A) (f : A → B) (Ha : a = a') : f a = f a' :=
eq.subst Ha rfl

definition congr_arg2 {A B C : Type} (a a' : A) (b b' : B) (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
eq.subst Ha (eq.subst Hb rfl)

section
  variables {A : Type} {a b c: A}
  open eq.ops

  definition trans_rel_left (R : A → A → Type) (H₁ : R a b) (H₂ : b = c) : R a c :=
  H₂ ▸ H₁

  definition trans_rel_right (R : A → A → Type) (H₁ : a = b) (H₂ : R b c) : R a c :=
  H₁⁻¹ ▸ H₂
end

attribute eq.subst [subst]
attribute eq.refl [refl]
attribute eq.trans [trans]
attribute eq.symm [symm]

namespace lift
  definition down_up.{l₁ l₂} {A : Type.{l₁}} (a : A) : down (up.{l₁ l₂} a) = a :=
  rfl

  definition up_down.{l₁ l₂} {A : Type.{l₁}} (a : lift.{l₁ l₂} A) : up (down a) = a :=
  lift.rec_on a (λ d, rfl)
end lift

/- ne -/

definition ne [reducible] {A : Type} (a b : A) := ¬(a = b)
notation a ≠ b := ne a b

namespace ne
  open eq.ops
  variable {A : Type}
  variables {a b : A}

  definition intro (H : a = b → empty) : a ≠ b := H

  definition elim (H : a ≠ b) : a = b → empty := H

  definition irrefl (H : a ≠ a) : empty := H rfl

  definition symm (H : a ≠ b) : b ≠ a :=
  assume (H₁ : b = a), H (H₁⁻¹)
end ne

definition empty_of_ne {A : Type} {a : A} : a ≠ a → empty := ne.irrefl

section
  open eq.ops
  variables {p : Type₀}

  definition ne_empty_of_self : p → p ≠ empty :=
  assume (Hp : p) (Heq : p = empty), Heq ▸ Hp

  definition ne_unit_of_not : ¬p → p ≠ unit :=
  assume (Hnp : ¬p) (Heq : p = unit), (Heq ▸ Hnp) star

  definition unit_ne_empty : ¬unit = empty :=
  ne_empty_of_self star
end

/- prod -/

abbreviation pair [constructor] := @prod.mk
infixr × := prod

variables {a b c d : Type}

attribute prod.rec [elim]
attribute prod.mk [intro!]

protected definition prod.elim [unfold 4] (H₁ : a × b) (H₂ : a → b → c) : c :=
prod.rec H₂ H₁

definition prod.swap [unfold 3] : a × b → b × a :=
prod.rec (λHa Hb, prod.mk Hb Ha)

/- sum -/

infixr ⊎ := sum
infixr + := sum

attribute sum.rec [elim]

protected definition sum.elim [unfold 4] (H₁ : a ⊎ b) (H₂ : a → c) (H₃ : b → c) : c :=
sum.rec H₂ H₃ H₁

definition non_contradictory_em (a : Type) : ¬¬(a ⊎ ¬a) :=
assume not_em : ¬(a ⊎ ¬a),
  have neg_a : ¬a, from
    assume pos_a : a, absurd (sum.inl pos_a) not_em,
  absurd (sum.inr neg_a) not_em

definition sum.swap : a ⊎ b → b ⊎ a := sum.rec sum.inr sum.inl


/- iff -/

definition iff (a b : Type) := (a → b) × (b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

definition iff.intro : (a → b) → (b → a) → (a ↔ b) := prod.mk

attribute iff.intro [intro!]

definition iff.elim : ((a → b) → (b → a) → c) → (a ↔ b) → c := prod.rec

attribute iff.elim [recursor 5] [elim]

definition iff.elim_left : (a ↔ b) → a → b := prod.pr1

definition iff.mp := @iff.elim_left

definition iff.elim_right : (a ↔ b) → b → a := prod.pr2

definition iff.mpr := @iff.elim_right

definition iff.refl [refl] (a : Type) : a ↔ a :=
iff.intro (assume H, H) (assume H, H)

definition iff.rfl {a : Type} : a ↔ a :=
iff.refl a

definition iff.trans [trans] (H₁ : a ↔ b) (H₂ : b ↔ c) : a ↔ c :=
iff.intro
  (assume Ha, iff.mp H₂ (iff.mp H₁ Ha))
  (assume Hc, iff.mpr H₁ (iff.mpr H₂ Hc))

definition iff.symm [symm] (H : a ↔ b) : b ↔ a :=
iff.intro (iff.elim_right H) (iff.elim_left H)

definition iff.comm : (a ↔ b) ↔ (b ↔ a) :=
iff.intro iff.symm iff.symm

definition iff.of_eq {a b : Type} (H : a = b) : a ↔ b :=
eq.rec_on H iff.rfl

definition not_iff_not_of_iff (H₁ : a ↔ b) : ¬a ↔ ¬b :=
iff.intro
 (assume (Hna : ¬ a) (Hb : b), Hna (iff.elim_right H₁ Hb))
 (assume (Hnb : ¬ b) (Ha : a), Hnb (iff.elim_left H₁ Ha))

definition of_iff_unit (H : a ↔ unit) : a :=
iff.mp (iff.symm H) star

definition not_of_iff_empty : (a ↔ empty) → ¬a := iff.mp

definition iff_unit_intro (H : a) : a ↔ unit :=
iff.intro
  (λ Hl, star)
  (λ Hr, H)

definition iff_empty_intro (H : ¬a) : a ↔ empty :=
iff.intro H (empty.rec _)

definition not_non_contradictory_iff_absurd (a : Type) : ¬¬¬a ↔ ¬a :=
iff.intro
  (λ (Hl : ¬¬¬a) (Ha : a), Hl (non_contradictory_intro Ha))
  absurd

definition imp_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a → b) ↔ (c → d) :=
iff.intro
  (λHab Hc, iff.mp H2 (Hab (iff.mpr H1 Hc)))
  (λHcd Ha, iff.mpr H2 (Hcd (iff.mp H1 Ha)))

definition not_not_intro (Ha : a) : ¬¬a :=
assume Hna : ¬a, Hna Ha

definition not_of_not_not_not (H : ¬¬¬a) : ¬a :=
λ Ha, absurd (not_not_intro Ha) H

definition not_unit [simp] : (¬ unit) ↔ empty :=
iff_empty_intro (not_not_intro star)

definition not_empty_iff [simp] : (¬ empty) ↔ unit :=
iff_unit_intro not_empty

definition not_congr [congr] (H : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (λ H₁ H₂, H₁ (iff.mpr H H₂)) (λ H₁ H₂, H₁ (iff.mp H H₂))

definition ne_self_iff_empty [simp] {A : Type} (a : A) : (not (a = a)) ↔ empty :=
iff.intro empty_of_ne empty.elim

definition eq_self_iff_unit [simp] {A : Type} (a : A) : (a = a) ↔ unit :=
iff_unit_intro rfl

definition iff_not_self [simp] (a : Type) : (a ↔ ¬a) ↔ empty :=
iff_empty_intro (λ H,
   have H' : ¬a, from (λ Ha, (iff.mp H Ha) Ha),
   H' (iff.mpr H H'))

definition not_iff_self [simp] (a : Type) : (¬a ↔ a) ↔ empty :=
iff_empty_intro (λ H,
   have H' : ¬a, from (λ Ha, (iff.mpr H Ha) Ha),
   H' (iff.mp H H'))

definition unit_iff_empty [simp] : (unit ↔ empty) ↔ empty :=
iff_empty_intro (λ H, iff.mp H star)

definition empty_iff_unit [simp] : (empty ↔ unit) ↔ empty :=
iff_empty_intro (λ H, iff.mpr H star)

definition empty_of_unit_iff_empty : (unit ↔ empty) → empty :=
assume H, iff.mp H star

/- prod simp rules -/
definition prod.imp (H₂ : a → c) (H₃ : b → d) : a × b → c × d :=
prod.rec (λHa Hb, prod.mk (H₂ Ha) (H₃ Hb))

definition prod_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a × b) ↔ (c × d) :=
iff.intro (prod.imp (iff.mp H1) (iff.mp H2)) (prod.imp (iff.mpr H1) (iff.mpr H2))

definition prod.comm [simp] : a × b ↔ b × a :=
iff.intro prod.swap prod.swap

definition prod.assoc [simp] : (a × b) × c ↔ a × (b × c) :=
iff.intro
  (prod.rec (λ H' Hc, prod.rec (λ Ha Hb, prod.mk Ha (prod.mk Hb Hc)) H'))
  (prod.rec (λ Ha, prod.rec (λ Hb Hc, prod.mk (prod.mk Ha Hb) Hc)))

definition prod.pr1_comm [simp] : a × (b × c) ↔ b × (a × c) :=
iff.trans (iff.symm !prod.assoc) (iff.trans (prod_congr !prod.comm !iff.refl) !prod.assoc)

definition prod_iff_left {a b : Type} (Hb : b) : (a × b) ↔ a :=
iff.intro prod.pr1 (λHa, prod.mk Ha Hb)

definition prod_iff_right {a b : Type} (Ha : a) : (a × b) ↔ b :=
iff.intro prod.pr2 (prod.mk Ha)

definition prod_unit [simp] (a : Type) : a × unit ↔ a :=
prod_iff_left star

definition unit_prod [simp] (a : Type) : unit × a ↔ a :=
prod_iff_right star

definition prod_empty [simp] (a : Type) : a × empty ↔ empty :=
iff_empty_intro prod.pr2

definition empty_prod [simp] (a : Type) : empty × a ↔ empty :=
iff_empty_intro prod.pr1

definition not_prod_self [simp] (a : Type) : (¬a × a) ↔ empty :=
iff_empty_intro (λ H, prod.elim H (λ H₁ H₂, absurd H₂ H₁))

definition prod_not_self [simp] (a : Type) : (a × ¬a) ↔ empty :=
iff_empty_intro (λ H, prod.elim H (λ H₁ H₂, absurd H₁ H₂))

definition prod_self [simp] (a : Type) : a × a ↔ a :=
iff.intro prod.pr1 (assume H, prod.mk H H)

/- sum simp rules -/

definition sum.imp (H₂ : a → c) (H₃ : b → d) : a ⊎ b → c ⊎ d :=
sum.rec (λ H, sum.inl (H₂ H)) (λ H, sum.inr (H₃ H))

definition sum.imp_left (H : a → b) : a ⊎ c → b ⊎ c :=
sum.imp H id

definition sum.imp_right (H : a → b) : c ⊎ a → c ⊎ b :=
sum.imp id H

definition sum_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a ⊎ b) ↔ (c ⊎ d) :=
iff.intro (sum.imp (iff.mp H1) (iff.mp H2)) (sum.imp (iff.mpr H1) (iff.mpr H2))

definition sum.comm [simp] : a ⊎ b ↔ b ⊎ a := iff.intro sum.swap sum.swap

definition sum.assoc [simp] : (a ⊎ b) ⊎ c ↔ a ⊎ (b ⊎ c) :=
iff.intro
  (sum.rec (sum.imp_right sum.inl) (λ H, sum.inr (sum.inr H)))
  (sum.rec (λ H, sum.inl (sum.inl H)) (sum.imp_left sum.inr))

definition sum.left_comm [simp] : a ⊎ (b ⊎ c) ↔ b ⊎ (a ⊎ c) :=
iff.trans (iff.symm !sum.assoc) (iff.trans (sum_congr !sum.comm !iff.refl) !sum.assoc)

definition sum_unit [simp] (a : Type) : a ⊎ unit ↔ unit :=
iff_unit_intro (sum.inr star)

definition unit_sum [simp] (a : Type) : unit ⊎ a ↔ unit :=
iff_unit_intro (sum.inl star)

definition sum_empty [simp] (a : Type) : a ⊎ empty ↔ a :=
iff.intro (sum.rec id empty.elim) sum.inl

definition empty_sum [simp] (a : Type) : empty ⊎ a ↔ a :=
iff.trans sum.comm !sum_empty

definition sum_self [simp] (a : Type) : a ⊎ a ↔ a :=
iff.intro (sum.rec id id) sum.inl

/- sum resolution rulse -/

definition sum.resolve_left {a b : Type} (H : a ⊎ b) (na : ¬ a) : b :=
  sum.elim H (λ Ha, absurd Ha na) id

definition sum.neg_resolve_left {a b : Type} (H : ¬ a ⊎ b) (Ha : a) : b :=
  sum.elim H (λ na, absurd Ha na) id

definition sum.resolve_right {a b : Type} (H : a ⊎ b) (nb : ¬ b) : a :=
  sum.elim H id (λ Hb, absurd Hb nb)

definition sum.neg_resolve_right {a b : Type} (H : a ⊎ ¬ b) (Hb : b) : a :=
  sum.elim H id (λ nb, absurd Hb nb)

/- iff simp rules -/

definition iff_unit [simp] (a : Type) : (a ↔ unit) ↔ a :=
iff.intro (assume H, iff.mpr H star) iff_unit_intro

definition unit_iff [simp] (a : Type) : (unit ↔ a) ↔ a :=
iff.trans iff.comm !iff_unit

definition iff_empty [simp] (a : Type) : (a ↔ empty) ↔ ¬ a :=
iff.intro prod.pr1 iff_empty_intro

definition empty_iff [simp] (a : Type) : (empty ↔ a) ↔ ¬ a :=
iff.trans iff.comm !iff_empty

definition iff_self [simp] (a : Type) : (a ↔ a) ↔ unit :=
iff_unit_intro iff.rfl

definition iff_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
prod_congr (imp_congr H1 H2) (imp_congr H2 H1)

/- decidable -/

inductive decidable [class] (p : Type) : Type :=
| inl :  p → decidable p
| inr : ¬p → decidable p

definition decidable_unit [instance] : decidable unit :=
decidable.inl star

definition decidable_empty [instance] : decidable empty :=
decidable.inr not_empty

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
definition dite (c : Type) [H : decidable c] {A : Type} : (c → A) → (¬ c → A) → A :=
decidable.rec_on H

/- if-then-else -/

definition ite (c : Type) [H : decidable c] {A : Type} (t e : A) : A :=
decidable.rec_on H (λ Hc, t) (λ Hnc, e)

namespace decidable
  variables {p q : Type}

  definition by_cases {q : Type} [C : decidable p] : (p → q) → (¬p → q) → q := !dite

  theorem em (p : Type) [H : decidable p] : p ⊎ ¬p := by_cases sum.inl sum.inr

  theorem by_contradiction [Hp : decidable p] (H : ¬p → empty) : p :=
  if H1 : p then H1 else empty.rec _ (H H1)
end decidable

section
  variables {p q : Type}
  open decidable
  definition  decidable_of_decidable_of_iff (Hp : decidable p) (H : p ↔ q) : decidable q :=
  if Hp : p then inl (iff.mp H Hp)
  else inr (iff.mp (not_iff_not_of_iff H) Hp)

  definition decidable_of_decidable_of_eq {p q : Type} (Hp : decidable p) (H : p = q)
    : decidable q :=
  decidable_of_decidable_of_iff Hp (iff.of_eq H)

  protected definition sum.by_cases [Hp : decidable p] [Hq : decidable q] {A : Type}
                                   (h : p ⊎ q) (h₁ : p → A) (h₂ : q → A) : A :=
  if hp : p then h₁ hp else
    if hq : q then h₂ hq else
      empty.rec _ (sum.elim h hp hq)
end

section
  variables {p q : Type}
  open decidable (rec_on inl inr)

  definition decidable_prod [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p × q) :=
  if hp : p then
    if hq : q then inl (prod.mk hp hq)
    else inr (assume H : p × q, hq (prod.pr2 H))
  else inr (assume H : p × q, hp (prod.pr1 H))

  definition decidable_sum [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ⊎ q) :=
  if hp : p then inl (sum.inl hp) else
    if hq : q then inl (sum.inr hq) else
      inr (sum.rec hp hq)

  definition decidable_not [instance] [Hp : decidable p] : decidable (¬p) :=
  if hp : p then inr (absurd hp) else inl hp

  definition decidable_implies [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p → q) :=
  if hp : p then
    if hq : q then inl (assume H, hq)
    else inr (assume H : p → q, absurd (H hp) hq)
  else inl (assume Hp, absurd Hp hp)

  definition decidable_iff [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ↔ q) :=
  decidable_prod

end

definition decidable_pred [reducible] {A : Type} (R : A   →   Type) := Π (a   : A), decidable (R a)
definition decidable_rel  [reducible] {A : Type} (R : A → A → Type) := Π (a b : A), decidable (R a b)
definition decidable_eq   [reducible] (A : Type) := decidable_rel (@eq A)
definition decidable_ne [instance] {A : Type} [H : decidable_eq A] (a b : A) : decidable (a ≠ b) :=
decidable_implies

namespace bool
  theorem ff_ne_tt : ff = tt → empty
  | [none]
end bool

open bool
definition is_dec_eq {A : Type} (p : A → A → bool) : Type   := Π ⦃x y : A⦄, p x y = tt → x = y
definition is_dec_refl {A : Type} (p : A → A → bool) : Type := Πx, p x x = tt

open decidable
protected definition bool.has_decidable_eq [instance] : Πa b : bool, decidable (a = b)
| ff ff := inl rfl
| ff tt := inr ff_ne_tt
| tt ff := inr (ne.symm ff_ne_tt)
| tt tt := inl rfl

definition decidable_eq_of_bool_pred {A : Type} {p : A → A → bool} (H₁ : is_dec_eq p) (H₂ : is_dec_refl p) : decidable_eq A :=
take x y : A, if Hp : p x y = tt then inl (H₁ Hp)
 else inr (assume Hxy : x = y, (eq.subst Hxy Hp) (H₂ y))

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

definition Type.is_inhabited [instance] : inhabited Type :=
inhabited.mk (lift unit)

definition inhabited_fun [instance] (A : Type) {B : Type} [H : inhabited B] : inhabited (A → B) :=
inhabited.rec_on H (λb, inhabited.mk (λa, b))

definition inhabited_Pi [instance] (A : Type) {B : A → Type} [H : Πx, inhabited (B x)] :
  inhabited (Πx, B x) :=
inhabited.mk (λa, !default)

protected definition bool.is_inhabited [instance] : inhabited bool :=
inhabited.mk ff

protected definition pos_num.is_inhabited [instance] : inhabited pos_num :=
inhabited.mk pos_num.one

protected definition num.is_inhabited [instance] : inhabited num :=
inhabited.mk num.zero

inductive nonempty [class] (A : Type) : Type :=
intro : A → nonempty A

protected definition nonempty.elim {A : Type} {B : Type} (H1 : nonempty A) (H2 : A → B) : B :=
nonempty.rec H2 H1

theorem nonempty_of_inhabited [instance] {A : Type} [H : inhabited A] : nonempty A :=
nonempty.intro !default

theorem nonempty_of_exists {A : Type} {P : A → Type} : (sigma P) → nonempty A :=
sigma.rec (λw H, nonempty.intro w)

/- subsingleton -/

inductive subsingleton [class] (A : Type) : Type :=
intro : (Π a b : A, a = b) → subsingleton A

protected definition subsingleton.elim {A : Type} [H : subsingleton A] : Π(a b : A), a = b :=
subsingleton.rec (λp, p) H

protected theorem rec_subsingleton {p : Type} [H : decidable p]
    {H1 : p → Type} {H2 : ¬p → Type}
    [H3 : Π(h : p), subsingleton (H1 h)] [H4 : Π(h : ¬p), subsingleton (H2 h)]
  : subsingleton (decidable.rec_on H H1 H2) :=
decidable.rec_on H (λh, H3 h) (λh, H4 h) --this can be proven using dependent version of "by_cases"

theorem if_pos {c : Type} [H : decidable c] (Hc : c) {A : Type} {t e : A} : (ite c t e) = t :=
decidable.rec
  (λ Hc : c,    eq.refl (@ite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

theorem if_neg {c : Type} [H : decidable c] (Hnc : ¬c) {A : Type} {t e : A} : (ite c t e) = e :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@ite c (decidable.inr Hnc) A t e))
  H

theorem if_t_t [simp] (c : Type) [H : decidable c] {A : Type} (t : A) : (ite c t t) = t :=
decidable.rec
  (λ Hc  : c,  eq.refl (@ite c (decidable.inl Hc)  A t t))
  (λ Hnc : ¬c, eq.refl (@ite c (decidable.inr Hnc) A t t))
  H

theorem implies_of_if_pos {c t e : Type} [H : decidable c] (h : ite c t e) : c → t :=
assume Hc, eq.rec_on (if_pos Hc) h

theorem implies_of_if_neg {c t e : Type} [H : decidable c] (h : ite c t e) : ¬c → e :=
assume Hnc, eq.rec_on (if_neg Hnc) h

theorem if_ctx_congr {A : Type} {b c : Type} [dec_b : decidable b] [dec_c : decidable c]
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

theorem if_congr [congr] {A : Type} {b c : Type} [dec_b : decidable b] [dec_c : decidable c]
                 {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr A b c dec_b dec_c x y u v h_c (λ h, h_t) (λ h, h_e)

theorem if_ctx_simp_congr {A : Type} {b c : Type} [dec_b : decidable b] {x y u v : A}
                        (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x y u v h_c h_t h_e

theorem if_simp_congr [congr] {A : Type} {b c : Type} [dec_b : decidable b] {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_simp_congr A b c dec_b x y u v h_c (λ h, h_t) (λ h, h_e)

definition if_unit [simp] {A : Type} (t e : A) : (if unit then t else e) = t :=
if_pos star

definition if_empty [simp] {A : Type} (t e : A) : (if empty then t else e) = e :=
if_neg not_empty

theorem if_ctx_congr_prop {b c x y u v : Type} [dec_b : decidable b] [dec_c : decidable c]
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

theorem if_congr_prop [congr] {b c x y u v : Type} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ ite c u v :=
if_ctx_congr_prop h_c (λ h, h_t) (λ h, h_e)

theorem if_ctx_simp_congr_prop {b c x y u v : Type} [dec_b : decidable b]
                               (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Type u v) :=
@if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff dec_b h_c) h_c h_t h_e

theorem if_simp_congr_prop [congr] {b c x y u v : Type} [dec_b : decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Type u v) :=
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (λ h, h_t) (λ h, h_e)

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
theorem dite_ite_eq (c : Type) [H : decidable c] {A : Type} (t : A) (e : A) : dite c (λh, t) (λh, e) = ite c t e :=
rfl

definition is_unit (c : Type) [H : decidable c] : Type₀ :=
if c then unit else empty

definition is_empty (c : Type) [H : decidable c] : Type₀ :=
if c then empty else unit

definition of_is_unit {c : Type} [H₁ : decidable c] (H₂ : is_unit c) : c :=
decidable.rec_on H₁ (λ Hc, Hc) (λ Hnc, empty.rec _ (if_neg Hnc ▸ H₂))

notation `dec_star` := of_is_unit star

theorem not_of_not_is_unit {c : Type} [H₁ : decidable c] (H₂ : ¬ is_unit c) : ¬ c :=
if Hc : c then absurd star (if_pos Hc ▸ H₂) else Hc

theorem not_of_is_empty {c : Type} [H₁ : decidable c] (H₂ : is_empty c) : ¬ c :=
if Hc : c then empty.rec _ (if_pos Hc ▸ H₂) else Hc

theorem of_not_is_empty {c : Type} [H₁ : decidable c] (H₂ : ¬ is_empty c) : c :=
if Hc : c then Hc else absurd star (if_neg Hc ▸ H₂)

-- The following symbols should not be considered in the pattern inference procedure used by
-- heuristic instantiation.
attribute prod sum not iff ite dite eq ne [no_pattern]

-- namespace used to collect congruence rules for "contextual simplification"
namespace contextual
  attribute if_ctx_simp_congr      [congr]
  attribute if_ctx_simp_congr_prop [congr]
end contextual
