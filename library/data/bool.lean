-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import general_notation
import logic.core.connectives logic.core.decidable logic.core.inhabited

open eq eq.ops decidable

inductive bool : Type :=
  ff : bool,
  tt : bool
namespace bool
  protected definition rec_on {C : bool → Type} (b : bool) (H₁ : C ff) (H₂ : C tt) : C b :=
  rec H₁ H₂ b

  protected definition cases_on {p : bool → Prop} (b : bool) (H₁ : p ff) (H₂ : p tt) : p b :=
  rec H₁ H₂ b

  definition cond {A : Type} (b : bool) (t e : A) :=
  rec_on b e t

  theorem dichotomy (b : bool) : b = ff ∨ b = tt :=
  cases_on b (or.inl rfl) (or.inr rfl)

  theorem cond_ff {A : Type} (t e : A) : cond ff t e = e :=
  rfl

  theorem cond_tt {A : Type} (t e : A) : cond tt t e = t :=
  rfl

  theorem ff_ne_tt : ¬ ff = tt :=
  assume H : ff = tt, absurd
    (calc true  = cond tt true false : (cond_tt _ _)⁻¹
            ... = cond ff true false : {H⁻¹}
            ... = false              : cond_ff _ _)
    true_ne_false

  definition or (a b : bool) :=
  rec_on a (rec_on b ff tt) tt

  theorem or_tt_left (a : bool) : or tt a = tt :=
  rfl

  infixl `||` := or

  theorem or_tt_right (a : bool) : a || tt = tt :=
  cases_on a rfl rfl

  theorem or_ff_left (a : bool) : ff || a = a :=
  cases_on a rfl rfl

  theorem or_ff_right (a : bool) : a || ff = a :=
  cases_on a rfl rfl

  theorem or_id (a : bool) : a || a = a :=
  cases_on a rfl rfl

  theorem or_comm (a b : bool) : a || b = b || a :=
  cases_on a
    (cases_on b rfl rfl)
    (cases_on b rfl rfl)

  theorem or_assoc (a b c : bool) : (a || b) || c = a || (b || c) :=
  cases_on a
    (calc (ff || b) || c = b || c         : {or_ff_left b}
                   ...   = ff || (b || c) : or_ff_left (b || c)⁻¹)
    (calc (tt || b) || c = tt || c        : {or_tt_left b}
                   ...   = tt             : or_tt_left c
                   ...   = tt || (b || c) : or_tt_left (b || c)⁻¹)

  theorem or_to_or {a b : bool} : a || b = tt → a = tt ∨ b = tt :=
  rec_on a
    (assume H : ff || b = tt,
      have Hb : b = tt, from (or_ff_left b) ▸ H,
      or.inr Hb)
    (assume H, or.inl rfl)

  definition and (a b : bool) :=
  rec_on a ff (rec_on b ff tt)

  infixl `&&` := and

  theorem and_ff_left (a : bool) : ff && a = ff :=
  rfl

  theorem and_tt_left (a : bool) : tt && a = a :=
  cases_on a rfl rfl

  theorem and_ff_right (a : bool) : a && ff = ff :=
  cases_on a rfl rfl

  theorem and_tt_right (a : bool) : a && tt = a :=
  cases_on a rfl rfl

  theorem and_id (a : bool) : a && a = a :=
  cases_on a rfl rfl

  theorem and_comm (a b : bool) : a && b = b && a :=
  cases_on a
    (cases_on b rfl rfl)
    (cases_on b rfl rfl)

  theorem and_assoc (a b c : bool) : (a && b) && c = a && (b && c) :=
  cases_on a
    (calc (ff && b) && c = ff && c        : {and_ff_left b}
                    ...  = ff             : and_ff_left c
                    ...  = ff && (b && c) : and_ff_left (b && c)⁻¹)
    (calc (tt && b) && c = b && c         : {and_tt_left b}
                    ...  = tt && (b && c) : and_tt_left (b && c)⁻¹)

  theorem and_eq_tt_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
  or.elim (dichotomy a)
    (assume H0 : a = ff,
      absurd
        (calc ff = ff && b : (and_ff_left _)⁻¹
             ... = a && b  : {H0⁻¹}
             ... = tt      : H)
        ff_ne_tt)
    (assume H1 : a = tt, H1)

  theorem and_eq_tt_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
  and_eq_tt_elim_left (and_comm b a ⬝ H)

  definition not (a : bool) :=
  rec_on a tt ff

  theorem bnot_bnot (a : bool) : not (not a) = a :=
  cases_on a rfl rfl

  theorem bnot_false : not ff = tt :=
  rfl

  theorem bnot_true  : not tt = ff :=
  rfl

  protected definition is_inhabited [instance] : inhabited bool :=
  inhabited.mk ff

  protected definition has_decidable_eq [instance] : decidable_eq bool :=
  take a b : bool,
    rec_on a
      (rec_on b (inl rfl) (inr ff_ne_tt))
      (rec_on b (inr (ne.symm ff_ne_tt)) (inl rfl))
end bool
