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
  by rec_simp

  theorem cond_ff [simp] {A : Type} (t e : A) : cond ff t e = e :=
  rfl

  theorem cond_tt [simp] {A : Type} (t e : A) : cond tt t e = t :=
  rfl

  theorem eq_tt_of_ne_ff : ∀ {a : bool}, a ≠ ff → a = tt :=
  by rec_simp

  theorem eq_ff_of_ne_tt : ∀ {a : bool}, a ≠ tt → a = ff :=
  by rec_simp

  theorem absurd_of_eq_ff_of_eq_tt {B : Prop} {a : bool} (H₁ : a = ff) (H₂ : a = tt) : B :=
  by rec_simp

  theorem tt_bor [simp] (a : bool) : bor tt a = tt :=
  rfl

  notation a || b := bor a b

  theorem bor_tt [simp] (a : bool) : a || tt = tt :=
  by rec_simp

  theorem ff_bor [simp] (a : bool) : ff || a = a :=
  by rec_simp

  theorem bor_ff [simp] (a : bool) : a || ff = a :=
  by rec_simp

  theorem bor_self [simp] (a : bool) : a || a = a :=
  by rec_simp

  theorem bor_comm [simp] (a b : bool) : a || b = b || a :=
  by rec_simp

  theorem bor_assoc [simp] (a b c : bool) : (a || b) || c = a || (b || c) :=
  by rec_simp

  theorem bor_left_comm [simp] (a b c : bool) : a || (b || c) = b || (a || c) :=
  by rec_simp

  theorem or_of_bor_eq {a b : bool} : a || b = tt → a = tt ∨ b = tt :=
  by rec_simp

  theorem bor_inl {a b : bool} (H : a = tt) : a || b = tt :=
  by rec_simp

  theorem bor_inr {a b : bool} (H : b = tt) : a || b = tt :=
  by rec_simp

  theorem ff_band [simp] (a : bool) : ff && a = ff :=
  rfl

  theorem tt_band [simp] (a : bool) : tt && a = a :=
  by rec_simp

  theorem band_ff [simp] (a : bool) : a && ff = ff :=
  by rec_simp

  theorem band_tt [simp] (a : bool) : a && tt = a :=
  by rec_simp

  theorem band_self [simp] (a : bool) : a && a = a :=
  by rec_simp

  theorem band_comm [simp] (a b : bool) : a && b = b && a :=
  by rec_simp

  theorem band_assoc [simp] (a b c : bool) : (a && b) && c = a && (b && c) :=
  by rec_simp

  theorem band_left_comm [simp] (a b c : bool) : a && (b && c) = b && (a && c) :=
  by rec_simp

  theorem band_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
  by rec_simp

  theorem band_intro {a b : bool} (H₁ : a = tt) (H₂ : b = tt) : a && b = tt :=
  by rec_simp

  theorem band_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
  by rec_simp

  theorem bnot_false [simp] : bnot ff = tt :=
  rfl

  theorem bnot_true [simp] : bnot tt = ff :=
  rfl

  theorem bnot_bnot [simp] (a : bool) : bnot (bnot a) = a :=
  by rec_simp

  theorem eq_tt_of_bnot_eq_ff {a : bool} : bnot a = ff → a = tt :=
  by rec_simp

  theorem eq_ff_of_bnot_eq_tt {a : bool} : bnot a = tt → a = ff :=
  by rec_simp

  definition bxor : bool → bool → bool
  | ff ff := ff
  | ff tt := tt
  | tt ff := tt
  | tt tt := ff

  lemma ff_bxor_ff [simp] : bxor ff ff = ff := rfl
  lemma ff_bxor_tt [simp] : bxor ff tt = tt := rfl
  lemma tt_bxor_ff [simp] : bxor tt ff = tt := rfl
  lemma tt_bxor_tt [simp] : bxor tt tt = ff := rfl

  lemma bxor_self [simp] (a : bool) : bxor a a = ff :=
  by rec_simp

  lemma bxor_ff [simp] (a : bool) : bxor a ff = a :=
  by rec_simp

  lemma bxor_tt [simp] (a : bool) : bxor a tt = bnot a :=
  by rec_simp

  lemma ff_bxor [simp] (a : bool) : bxor ff a = a :=
  by rec_simp

  lemma tt_bxor [simp] (a : bool) : bxor tt a = bnot a :=
  by rec_simp

  lemma bxor_comm [simp] (a b : bool) : bxor a b = bxor b a :=
  by rec_simp

  lemma bxor_assoc [simp] (a b c : bool) : bxor (bxor a b) c = bxor a (bxor b c) :=
  by rec_simp

  lemma bxor_left_comm [simp] (a b c : bool) : bxor a (bxor b c) = bxor b (bxor a c) :=
  by rec_simp
end bool
