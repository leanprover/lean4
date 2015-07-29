/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import logic.quantifiers logic.eq
import data.subtype data.sum

open subtype inhabited nonempty

/- the axiom -/

-- In the presence of classical logic, we could prove this from a weaker statement:
-- axiom indefinite_description {A : Type} {P : A->Prop} (H : ∃x, P x) : {x : A, P x}
axiom strong_indefinite_description {A : Type} (P : A → Prop) (H : nonempty A) :
  { x | (∃y : A, P y) → P x}

theorem exists_true_of_nonempty {A : Type} (H : nonempty A) : ∃x : A, true :=
nonempty.elim H (take x, exists.intro x trivial)

noncomputable definition inhabited_of_nonempty {A : Type} (H : nonempty A) : inhabited A :=
let u : {x | (∃y : A, true) → true} := strong_indefinite_description (λa, true) H in
inhabited.mk (elt_of u)

noncomputable definition inhabited_of_exists {A : Type} {P : A → Prop} (H : ∃x, P x) : inhabited A :=
inhabited_of_nonempty (obtain w Hw, from H, nonempty.intro w)

/- the Hilbert epsilon function -/

noncomputable definition epsilon {A : Type} [H : nonempty A] (P : A → Prop) : A :=
let u : {x | (∃y, P y) → P x} :=
  strong_indefinite_description P H in
elt_of u

theorem epsilon_spec_aux {A : Type} (H : nonempty A) (P : A → Prop) (Hex : ∃y, P y) :
    P (@epsilon A H P) :=
let u : {x | (∃y, P y) → P x} :=
  strong_indefinite_description P H in
have aux : (∃y, P y) → P (elt_of (strong_indefinite_description P H)), from has_property u,
aux Hex

theorem epsilon_spec {A : Type} {P : A → Prop} (Hex : ∃y, P y) :
    P (@epsilon A (nonempty_of_exists Hex) P) :=
epsilon_spec_aux (nonempty_of_exists Hex) P Hex

theorem epsilon_singleton {A : Type} (a : A) : @epsilon A (nonempty.intro a) (λx, x = a) = a :=
epsilon_spec (exists.intro a (eq.refl a))

noncomputable definition some {A : Type} {P : A → Prop} (H : ∃x, P x) : A :=
@epsilon A (nonempty_of_exists H) P

theorem some_spec {A : Type} {P : A → Prop} (H : ∃x, P x) : P (some H) :=
epsilon_spec H

/- the axiom of choice -/

theorem axiom_of_choice {A : Type} {B : A → Type} {R : Πx, B x → Prop} (H : ∀x, ∃y, R x y) :
  ∃f, ∀x, R x (f x) :=
have H : ∀x, R x (some (H x)), from take x, some_spec (H x),
exists.intro _ H

theorem skolem {A : Type} {B : A → Type} {P : Πx, B x → Prop} :
  (∀x, ∃y, P x y) ↔ ∃f, (∀x, P x (f x)) :=
iff.intro
  (assume H : (∀x, ∃y, P x y), axiom_of_choice H)
  (assume H : (∃f, (∀x, P x (f x))),
    take x, obtain (fw : ∀x, B x) (Hw : ∀x, P x (fw x)), from H,
      exists.intro (fw x) (Hw x))

/-
Prove excluded middle using Hilbert's choice
The proof follows Diaconescu proof that shows that the axiom of choice implies the excluded middle.
-/
section diaconescu
open eq.ops
parameter  p : Prop

private definition U (x : Prop) : Prop := x = true ∨ p
private definition V (x : Prop) : Prop := x = false ∨ p

private noncomputable definition u := epsilon U
private noncomputable definition v := epsilon V

private lemma u_def : U u :=
epsilon_spec (exists.intro true (or.inl rfl))

private lemma v_def : V v :=
epsilon_spec (exists.intro false (or.inl rfl))

private lemma not_uv_or_p : ¬(u = v) ∨ p :=
or.elim u_def
  (assume Hut : u = true,
    or.elim v_def
      (assume Hvf : v = false,
        have Hne : ¬(u = v), from Hvf⁻¹ ▸ Hut⁻¹ ▸ true_ne_false,
        or.inl Hne)
      (assume Hp : p, or.inr Hp))
  (assume Hp : p, or.inr Hp)

private lemma p_implies_uv : p → u = v :=
assume Hp : p,
have Hpred : U = V, from
  funext (take x : Prop,
    have Hl : (x = true ∨ p) → (x = false ∨ p), from
      assume A, or.inr Hp,
    have Hr : (x = false ∨ p) → (x = true ∨ p), from
      assume A, or.inr Hp,
    show (x = true ∨ p) = (x = false ∨ p), from
      propext (iff.intro Hl Hr)),
have H' : epsilon U = epsilon V, from Hpred ▸ rfl,
show u = v, from H'

theorem em : p ∨ ¬p :=
have H : ¬(u = v) → ¬p, from mt p_implies_uv,
  or.elim not_uv_or_p
    (assume Hne : ¬(u = v), or.inr (H Hne))
    (assume Hp : p, or.inl Hp)
end diaconescu

theorem prop_complete (a : Prop) : a = true ∨ a = false :=
or.elim (em a)
  (λ t, or.inl (propext (iff.intro (λ h, trivial) (λ h, t))))
  (λ f, or.inr (propext (iff.intro (λ h, absurd h f) (λ h, false.elim h))))

definition eq_true_or_eq_false := prop_complete

section aux
open eq.ops
theorem cases_true_false (P : Prop → Prop) (H1 : P true) (H2 : P false) (a : Prop) : P a :=
or.elim (prop_complete a)
  (assume Ht : a = true,  Ht⁻¹ ▸ H1)
  (assume Hf : a = false, Hf⁻¹ ▸ H2)

theorem cases_on (a : Prop) {P : Prop → Prop} (H1 : P true) (H2 : P false) : P a :=
cases_true_false P H1 H2 a

-- this supercedes by_cases in decidable
definition by_cases {p q : Prop} (Hpq : p → q) (Hnpq : ¬p → q) : q :=
or.elim (em p) (assume Hp, Hpq Hp) (assume Hnp, Hnpq Hnp)

-- this supercedes by_contradiction in decidable
theorem by_contradiction {p : Prop} (H : ¬p → false) : p :=
by_cases
  (assume H1 : p, H1)
  (assume H1 : ¬p, false.rec _ (H H1))

theorem eq_false_or_eq_true (a : Prop) : a = false ∨ a = true :=
cases_true_false (λ x, x = false ∨ x = true)
  (or.inr rfl)
  (or.inl rfl)
  a

theorem eq.of_iff {a b : Prop} (H : a ↔ b) : a = b :=
iff.elim (assume H1 H2, propext (iff.intro H1 H2)) H

theorem iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) :=
propext (iff.intro
  (assume H, eq.of_iff H)
  (assume H, iff.of_eq H))

end aux

/- All propositions are decidable -/
section all_decidable
open decidable sum

noncomputable definition decidable_inhabited [instance] [priority 0] (a : Prop) : inhabited (decidable a) :=
inhabited_of_nonempty
  (or.elim (em a)
    (assume Ha, nonempty.intro (inl Ha))
    (assume Hna, nonempty.intro (inr Hna)))

noncomputable definition prop_decidable [instance] [priority 0] (a : Prop) : decidable a :=
arbitrary (decidable a)

noncomputable definition type_decidable (A : Type) : A + (A → false) :=
match prop_decidable (nonempty A) with
| inl Hp := sum.inl (inhabited.value (inhabited_of_nonempty Hp))
| inr Hn := sum.inr (λ a, absurd (nonempty.intro a) Hn)
end
end all_decidable
