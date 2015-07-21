/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

import logic.eq
open eq eq.ops decidable

namespace bool
  local attribute bor [reducible]
  local attribute band [reducible]

  theorem dichotomy (b : bool) : b = ff ∨ b = tt :=
  bool.cases_on b (or.inl rfl) (or.inr rfl)

  theorem cond_ff {A : Type} (t e : A) : cond ff t e = e :=
  rfl

  theorem cond_tt {A : Type} (t e : A) : cond tt t e = t :=
  rfl

  theorem eq_tt_of_ne_ff : ∀ {a : bool}, a ≠ ff → a = tt
  | @eq_tt_of_ne_ff tt H := rfl
  | @eq_tt_of_ne_ff ff H := absurd rfl H

  theorem eq_ff_of_ne_tt : ∀ {a : bool}, a ≠ tt → a = ff
  | @eq_ff_of_ne_tt tt H := absurd rfl H
  | @eq_ff_of_ne_tt ff H := rfl

  theorem absurd_of_eq_ff_of_eq_tt {B : Prop} {a : bool} (H₁ : a = ff) (H₂ : a = tt) : B :=
  absurd (H₁⁻¹ ⬝ H₂) ff_ne_tt

  theorem tt_bor (a : bool) : bor tt a = tt :=
  rfl

  notation a || b := bor a b

  theorem bor_tt (a : bool) : a || tt = tt :=
  bool.cases_on a rfl rfl

  theorem ff_bor (a : bool) : ff || a = a :=
  bool.cases_on a rfl rfl

  theorem bor_ff (a : bool) : a || ff = a :=
  bool.cases_on a rfl rfl

  theorem bor_self (a : bool) : a || a = a :=
  bool.cases_on a rfl rfl

  theorem bor.comm (a b : bool) : a || b = b || a :=
  by cases a; repeat (cases b | reflexivity)

  theorem bor.assoc (a b c : bool) : (a || b) || c = a || (b || c) :=
  match a with
  | ff := by rewrite *ff_bor
  | tt := by rewrite *tt_bor
  end

  theorem or_of_bor_eq {a b : bool} : a || b = tt → a = tt ∨ b = tt :=
  bool.rec_on a
    (suppose ff || b = tt,
      have b = tt, from !ff_bor ▸ this,
      or.inr this)
    (suppose tt || b = tt,
      or.inl rfl)

  theorem bor_inl {a b : bool} (H : a = tt) : a || b = tt :=
  by rewrite H

  theorem bor_inr {a b : bool} (H : b = tt) : a || b = tt :=
  bool.rec_on a (by rewrite H) (by rewrite H)

  theorem ff_band (a : bool) : ff && a = ff :=
  rfl

  theorem tt_band (a : bool) : tt && a = a :=
  bool.cases_on a rfl rfl

  theorem band_ff (a : bool) : a && ff = ff :=
  bool.cases_on a rfl rfl

  theorem band_tt (a : bool) : a && tt = a :=
  bool.cases_on a rfl rfl

  theorem band_self (a : bool) : a && a = a :=
  bool.cases_on a rfl rfl

  theorem band.comm (a b : bool) : a && b = b && a :=
  bool.cases_on a
    (bool.cases_on b rfl rfl)
    (bool.cases_on b rfl rfl)

  theorem band.assoc (a b c : bool) : (a && b) && c = a && (b && c) :=
  match a with
  | ff := by rewrite *ff_band
  | tt := by rewrite *tt_band
  end

  theorem band_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
  or.elim (dichotomy a)
    (suppose a = ff,
      absurd
        (calc ff = ff && b : ff_band
             ... = a && b  : this
             ... = tt      : H)
        ff_ne_tt)
    (suppose a = tt, this)

  theorem band_intro {a b : bool} (H₁ : a = tt) (H₂ : b = tt) : a && b = tt :=
  by rewrite [H₁, H₂]

  theorem band_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
  band_elim_left (!band.comm ⬝ H)

  theorem bnot_bnot (a : bool) : bnot (bnot a) = a :=
  bool.cases_on a rfl rfl

  theorem bnot_false : bnot ff = tt :=
  rfl

  theorem bnot_true  : bnot tt = ff :=
  rfl

  theorem eq_tt_of_bnot_eq_ff {a : bool} : bnot a = ff → a = tt :=
  bool.cases_on a (by contradiction) (λ h, rfl)

  theorem eq_ff_of_bnot_eq_tt {a : bool} : bnot a = tt → a = ff :=
  bool.cases_on a (λ h, rfl) (by contradiction)
end bool
