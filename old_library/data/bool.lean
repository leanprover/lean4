/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import logic.eq

namespace bool
  local attribute bor [reducible]
  local attribute band [reducible]

  theorem dichotomy (b : bool) : b = ff ∨ b = tt :=
  sorry -- by rec_simp

  attribute [simp]
  theorem cond_ff {A : Type} (t e : A) : cond ff t e = e :=
  rfl

  attribute [simp]
  theorem cond_tt {A : Type} (t e : A) : cond tt t e = t :=
  rfl

  theorem eq_tt_of_ne_ff : ∀ {a : bool}, a ≠ ff → a = tt :=
  sorry -- by rec_simp

  theorem eq_ff_of_ne_tt : ∀ {a : bool}, a ≠ tt → a = ff :=
  sorry -- by rec_simp

  theorem absurd_of_eq_ff_of_eq_tt {B : Prop} {a : bool} (H₁ : a = ff) (H₂ : a = tt) : B :=
  sorry -- by rec_simp

  attribute [simp]
  theorem tt_bor (a : bool) : bor tt a = tt :=
  rfl

  notation a || b := bor a b

  attribute [simp]
  theorem bor_tt (a : bool) : a || tt = tt :=
  sorry -- by rec_simp

  attribute [simp]
  theorem ff_bor (a : bool) : ff || a = a :=
  sorry -- by rec_simp

  attribute [simp]
  theorem bor_ff (a : bool) : a || ff = a :=
  sorry -- by rec_simp

  attribute [simp]
  theorem bor_self (a : bool) : a || a = a :=
  sorry -- by rec_simp

  attribute [simp]
  theorem bor_comm (a b : bool) : a || b = b || a :=
  sorry -- by rec_simp

  attribute [simp]
  theorem bor_assoc (a b c : bool) : (a || b) || c = a || (b || c) :=
  sorry -- by rec_simp

  attribute [simp]
  theorem bor_left_comm (a b c : bool) : a || (b || c) = b || (a || c) :=
  sorry -- by rec_simp

  theorem or_of_bor_eq {a b : bool} : a || b = tt → a = tt ∨ b = tt :=
  sorry -- by rec_simp

  theorem bor_inl {a b : bool} (H : a = tt) : a || b = tt :=
  sorry -- by rec_simp

  theorem bor_inr {a b : bool} (H : b = tt) : a || b = tt :=
  sorry -- by rec_simp

  attribute [simp]
  theorem ff_band (a : bool) : ff && a = ff :=
  rfl

  attribute [simp]
  theorem tt_band (a : bool) : tt && a = a :=
  sorry -- by rec_simp

  attribute [simp]
  theorem band_ff (a : bool) : a && ff = ff :=
  sorry -- by rec_simp

  attribute [simp]
  theorem band_tt (a : bool) : a && tt = a :=
  sorry -- by rec_simp

  attribute [simp]
  theorem band_self (a : bool) : a && a = a :=
  sorry -- by rec_simp

  attribute [simp]
  theorem band_comm (a b : bool) : a && b = b && a :=
  sorry -- by rec_simp

  attribute [simp]
  theorem band_assoc (a b c : bool) : (a && b) && c = a && (b && c) :=
  sorry -- by rec_simp

  attribute [simp]
  theorem band_left_comm (a b c : bool) : a && (b && c) = b && (a && c) :=
  sorry -- by rec_simp

  theorem band_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
  sorry -- by rec_simp

  theorem band_intro {a b : bool} (H₁ : a = tt) (H₂ : b = tt) : a && b = tt :=
  sorry -- by rec_simp

  theorem band_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
  sorry -- by rec_simp

  attribute [simp]
  theorem bnot_false : bnot ff = tt :=
  rfl

  attribute [simp]
  theorem bnot_true : bnot tt = ff :=
  rfl

  attribute [simp]
  theorem bnot_bnot (a : bool) : bnot (bnot a) = a :=
  sorry -- by rec_simp

  theorem eq_tt_of_bnot_eq_ff {a : bool} : bnot a = ff → a = tt :=
  sorry -- by rec_simp

  theorem eq_ff_of_bnot_eq_tt {a : bool} : bnot a = tt → a = ff :=
  sorry -- by rec_simp

  definition bxor : bool → bool → bool
  | ff ff := ff
  | ff tt := tt
  | tt ff := tt
  | tt tt := ff

  attribute [simp]
  lemma ff_bxor_ff : bxor ff ff = ff := rfl
  attribute [simp]
  lemma ff_bxor_tt : bxor ff tt = tt := rfl
  attribute [simp]
  lemma tt_bxor_ff : bxor tt ff = tt := rfl
  attribute [simp]
  lemma tt_bxor_tt : bxor tt tt = ff := rfl

  attribute [simp]
  lemma bxor_self (a : bool) : bxor a a = ff :=
  sorry -- by rec_simp

  attribute [simp]
  lemma bxor_ff (a : bool) : bxor a ff = a :=
  sorry -- by rec_simp

  attribute [simp]
  lemma bxor_tt (a : bool) : bxor a tt = bnot a :=
  sorry -- by rec_simp

  attribute [simp]
  lemma ff_bxor (a : bool) : bxor ff a = a :=
  sorry -- by rec_simp

  attribute [simp]
  lemma tt_bxor (a : bool) : bxor tt a = bnot a :=
  sorry -- by rec_simp

  attribute [simp]
  lemma bxor_comm (a b : bool) : bxor a b = bxor b a :=
  sorry -- by rec_simp

  attribute [simp]
  lemma bxor_assoc (a b c : bool) : bxor (bxor a b) c = bxor a (bxor b c) :=
  sorry -- by rec_simp

  attribute [simp]
  lemma bxor_left_comm (a b c : bool) : bxor a (bxor b c) = bxor b (bxor a c) :=
  sorry -- by rec_simp
end bool
