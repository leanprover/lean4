/-
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Jakob von Raumer
-/

prelude
import .num .wf

-- Empty type
-- ----------

namespace empty

  protected theorem elim {A : Type} (H : empty) : A :=
  empty.rec (λe, A) H

end empty

protected definition empty.has_decidable_eq [instance] : decidable_eq empty :=
take (a b : empty), decidable.inl (!empty.elim a)

-- Unit type
-- ---------

namespace unit

  notation `⋆` := star

end unit

-- Sigma type
-- ----------

notation `Σ` binders `,` r:(scoped P, sigma P) := r

namespace sigma
  notation `⟨`:max t:(foldr `,` (e r, mk e r)) `⟩`:0 := t --input ⟨ ⟩ as \< \>

  namespace ops
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  abbreviation pr₁ := @pr1
  abbreviation pr₂ := @pr2
  end ops
end sigma

-- Sum type
-- --------

namespace sum
  infixr ⊎ := sum
  infixr + := sum
  namespace low_precedence_plus
    reserve infixr `+`:25  -- conflicts with notation for addition
    infixr `+` := sum
  end low_precedence_plus

  variables {a b c d : Type}
  definition sum_of_sum_of_imp_of_imp (H₁ : a ⊎ b) (H₂ : a → c) (H₃ : b → d) : c ⊎ d :=
  sum.rec_on H₁
    (assume Ha : a, sum.inl (H₂ Ha))
    (assume Hb : b, sum.inr (H₃ Hb))

  definition sum_of_sum_of_imp_left (H₁ : a ⊎ c) (H : a → b) : b ⊎ c :=
  sum.rec_on H₁
    (assume H₂ : a, sum.inl (H H₂))
    (assume H₂ : c, sum.inr H₂)

  definition sum_of_sum_of_imp_right (H₁ : c ⊎ a) (H : a → b) : c ⊎ b :=
  sum.rec_on H₁
    (assume H₂ : c, sum.inl H₂)
    (assume H₂ : a, sum.inr (H H₂))
end sum

-- Product type
-- ------------

abbreviation pair [constructor] := @prod.mk

namespace prod

  -- notation for n-ary tuples
  notation `(` h `,` t:(foldl `,` (e r, prod.mk r e) h) `)` := t
  infixr × := prod

  namespace ops
  infixr [parsing-only] * := prod
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  abbreviation pr₁ := @pr1
  abbreviation pr₂ := @pr2
  end ops

  namespace low_precedence_times

    reserve infixr `*`:30  -- conflicts with notation for multiplication
    infixr `*` := prod

  end low_precedence_times

  open prod.ops

  definition flip [unfold 3] {A B : Type} (a : A × B) : B × A := pair (pr2 a) (pr1 a)

  open well_founded

  section
  variables {A B : Type}
  variable  (Ra  : A → A → Type)
  variable  (Rb  : B → B → Type)

  -- Lexicographical order based on Ra and Rb
  inductive lex : A × B → A × B → Type :=
  | left  : ∀{a₁ b₁} a₂ b₂, Ra a₁ a₂ → lex (a₁, b₁) (a₂, b₂)
  | right : ∀a {b₁ b₂},     Rb b₁ b₂ → lex (a, b₁)  (a, b₂)

  -- Relational product based on Ra and Rb
  inductive rprod : A × B → A × B → Type :=
  intro : ∀{a₁ b₁ a₂ b₂}, Ra a₁ a₂ → Rb b₁ b₂ → rprod (a₁, b₁) (a₂, b₂)
  end

  section
  parameters {A B : Type}
  parameters {Ra  : A → A → Type} {Rb  : B → B → Type}
  local infix `≺`:50 := lex Ra Rb

  definition lex.accessible {a} (aca : acc Ra a) (acb : ∀b, acc Rb b): ∀b, acc (lex Ra Rb) (a, b) :=
  acc.rec_on aca
    (λxa aca (iHa : ∀y, Ra y xa → ∀b, acc (lex Ra Rb) (y, b)),
      λb, acc.rec_on (acb b)
        (λxb acb
          (iHb : ∀y, Rb y xb → acc (lex Ra Rb) (xa, y)),
          acc.intro (xa, xb) (λp (lt : p ≺ (xa, xb)),
            have aux : xa = xa → xb = xb → acc (lex Ra Rb) p, from
              @prod.lex.rec_on A B Ra Rb (λp₁ p₂ h, pr₁ p₂ = xa → pr₂ p₂ = xb → acc (lex Ra Rb) p₁)
                               p (xa, xb) lt
                (λa₁ b₁ a₂ b₂ (H : Ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a₁, b₁), from
                  have Ra₁  : Ra a₁ xa, from eq.rec_on eq₂ H,
                  iHa a₁ Ra₁ b₁)
                (λa b₁ b₂ (H : Rb b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a, b₁), from
                  have Rb₁  : Rb b₁ xb, from eq.rec_on eq₃ H,
                  have eq₂' : xa = a, from eq.rec_on eq₂ rfl,
                  eq.rec_on eq₂' (iHb b₁ Rb₁)),
            aux rfl rfl)))

  -- The lexicographical order of well founded relations is well-founded
  definition lex.wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (lex Ra Rb) :=
  well_founded.intro (λp, destruct p (λa b, lex.accessible (Ha a) (well_founded.apply Hb) b))

  -- Relational product is a subrelation of the lex
  definition rprod.sub_lex : ∀ a b, rprod Ra Rb a b → lex Ra Rb a b :=
  λa b H, prod.rprod.rec_on H (λ a₁ b₁ a₂ b₂ H₁ H₂, lex.left Rb a₂ b₂ H₁)

  -- The relational product of well founded relations is well-founded
  definition rprod.wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (rprod Ra Rb) :=
  subrelation.wf (rprod.sub_lex) (lex.wf Ha Hb)

  end

end prod

/- logic using prod and sum -/

variables {a b c d : Type}
open prod sum unit

/- prod -/

definition not_prod_of_not_left (b : Type) (Hna : ¬a) : ¬(a × b) :=
assume H : a × b, absurd (pr1 H) Hna

definition not_prod_of_not_right (a : Type) {b : Type} (Hnb : ¬b) : ¬(a × b) :=
assume H : a × b, absurd (pr2 H) Hnb

definition prod.swap (H : a × b) : b × a :=
pair (pr2 H) (pr1 H)

definition prod_of_prod_of_imp_of_imp (H₁ : a × b) (H₂ : a → c) (H₃ : b → d) : c × d :=
by cases H₁ with aa bb; exact (H₂ aa, H₃ bb)

definition prod_of_prod_of_imp_left (H₁ : a × c) (H : a → b) : b × c :=
by cases H₁ with aa cc; exact (H aa, cc)

definition prod_of_prod_of_imp_right (H₁ : c × a) (H : a → b) : c × b :=
by cases H₁ with cc aa; exact (cc, H aa)

definition prod.comm : a × b ↔ b × a :=
iff.intro (λH, prod.swap H) (λH, prod.swap H)

definition prod.assoc : (a × b) × c ↔ a × (b × c) :=
iff.intro
  (assume H, pair
    (pr1 (pr1 H))
    (pair (pr2 (pr1 H)) (pr2 H)))
  (assume H, pair
    (pair (pr1 H) (pr1 (pr2 H)))
    (pr2 (pr2 H)))

definition prod_unit (a : Type) : a × unit ↔ a :=
iff.intro (assume H, pr1 H) (assume H, pair H star)

definition unit_prod (a : Type) : unit × a ↔ a :=
iff.intro (assume H, pr2 H) (assume H, pair star H)

definition prod_empty (a : Type) : a × empty ↔ empty :=
iff.intro (assume H, pr2 H) (assume H, !empty.elim H)

definition empty_prod (a : Type) : empty × a ↔ empty :=
iff.intro (assume H, pr1 H) (assume H, !empty.elim H)

definition prod_self (a : Type) : a × a ↔ a :=
iff.intro (assume H, pr1 H) (assume H, pair H H)

/- sum -/

definition not_sum (Hna : ¬a) (Hnb : ¬b) : ¬(a ⊎ b) :=
assume H : a ⊎ b, sum.rec_on H
  (assume Ha, absurd Ha Hna)
  (assume Hb, absurd Hb Hnb)

definition sum_of_sum_of_imp_of_imp (H₁ : a ⊎ b) (H₂ : a → c) (H₃ : b → d) : c ⊎ d :=
sum.rec_on H₁
  (assume Ha : a, sum.inl (H₂ Ha))
  (assume Hb : b, sum.inr (H₃ Hb))

definition sum_of_sum_of_imp_left (H₁ : a ⊎ c) (H : a → b) : b ⊎ c :=
sum.rec_on H₁
  (assume H₂ : a, sum.inl (H H₂))
  (assume H₂ : c, sum.inr H₂)

definition sum_of_sum_of_imp_right (H₁ : c ⊎ a) (H : a → b) : c ⊎ b :=
sum.rec_on H₁
  (assume H₂ : c, sum.inl H₂)
  (assume H₂ : a, sum.inr (H H₂))

definition sum.elim3 (H : a ⊎ b ⊎ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
sum.rec_on H Ha (assume H₂, sum.rec_on H₂ Hb Hc)

definition sum_resolve_right (H₁ : a ⊎ b) (H₂ : ¬a) : b :=
sum.rec_on H₁ (assume Ha, absurd Ha H₂) (assume Hb, Hb)

definition sum_resolve_left (H₁ : a ⊎ b) (H₂ : ¬b) : a :=
sum.rec_on H₁ (assume Ha, Ha) (assume Hb, absurd Hb H₂)

definition sum.swap (H : a ⊎ b) : b ⊎ a :=
sum.rec_on H (assume Ha, sum.inr Ha) (assume Hb, sum.inl Hb)

definition sum.comm : a ⊎ b ↔ b ⊎ a :=
iff.intro (λH, sum.swap H) (λH, sum.swap H)

definition sum.assoc : (a ⊎ b) ⊎ c ↔ a ⊎ (b ⊎ c) :=
iff.intro
  (assume H, sum.rec_on H
    (assume H₁, sum.rec_on H₁
      (assume Ha, sum.inl Ha)
      (assume Hb, sum.inr (sum.inl Hb)))
    (assume Hc, sum.inr (sum.inr Hc)))
  (assume H, sum.rec_on H
    (assume Ha, (sum.inl (sum.inl Ha)))
    (assume H₁, sum.rec_on H₁
      (assume Hb, sum.inl (sum.inr Hb))
      (assume Hc, sum.inr Hc)))

definition sum_unit (a : Type) : a ⊎ unit ↔ unit :=
iff.intro (assume H, star) (assume H, sum.inr H)

definition unit_sum (a : Type) : unit ⊎ a ↔ unit :=
iff.intro (assume H, star) (assume H, sum.inl H)

definition sum_empty (a : Type) : a ⊎ empty ↔ a :=
iff.intro
  (assume H, sum.rec_on H (assume H1 : a, H1) (assume H1 : empty, !empty.elim H1))
  (assume H, sum.inl H)

definition empty_sum (a : Type) : empty ⊎ a ↔ a :=
iff.intro
  (assume H, sum.rec_on H (assume H1 : empty, !empty.elim H1) (assume H1 : a, H1))
  (assume H, sum.inr H)

definition sum_self (a : Type) : a ⊎ a ↔ a :=
iff.intro
  (assume H, sum.rec_on H (assume H1, H1) (assume H1, H1))
  (assume H, sum.inl H)
