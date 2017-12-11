/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
universe u

meta def tactic.interactive.blast_disjs : tactic unit :=
`[cases_type* or]

namespace rbnode
variables {α : Type u}

open color nat

inductive is_node_of : rbnode α → rbnode α → α → rbnode α → Prop
| of_red   (l v r) : is_node_of (red_node l v r)    l v r
| of_black (l v r) : is_node_of (black_node l v r)  l v r

def lift (lt : α → α → Prop) : option α → option α → Prop
| (some a) (some b) := lt a b
| _         _       := true

inductive is_searchable (lt : α → α → Prop) : rbnode α → option α → option α → Prop
| leaf_s  {lo hi} (hlt : lift lt lo hi) : is_searchable leaf lo hi
| red_s   {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) : is_searchable (red_node l v r) lo hi
| black_s {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) : is_searchable (black_node l v r) lo hi

meta def is_searchable_tactic : tactic unit :=
`[
   constructor_matching*
     [is_searchable _ leaf _ _,
      is_searchable _ (red_node _ _ _) _ _,
      is_searchable _ (black_node _ _ _) _ _];
   cases_matching*
     [is_searchable _ leaf _ _,
      is_searchable _ (red_node _ _ _) _ _,
      is_searchable _ (black_node _ _ _) _ _];
   try { assumption }
]

open rbnode (mem)
open is_searchable

section is_searchable_lemmas
variable {lt : α → α → Prop}

lemma lo_lt_hi {t : rbnode α} {lt} [is_trans α lt] : ∀ {lo hi}, is_searchable lt t lo hi → lift lt lo hi :=
begin
  induction t; intros lo hi hs,
  case leaf { cases hs, assumption },
  all_goals {
    cases hs,
    have h₁ := t_ih_lchild hs_hs₁,
    have h₂ := t_ih_rchild hs_hs₂,
    cases lo; cases hi; simp [lift] at *,
    apply trans_of lt h₁ h₂,
  }
end

variable [decidable_rel lt]

lemma is_searchable_of_is_searchable_of_incomp [is_strict_weak_order α lt] {t} : ∀ {lo hi hi'} (hc : ¬ lt hi' hi ∧ ¬ lt hi hi') (hs : is_searchable lt t lo (some hi)), is_searchable lt t lo (some hi') :=
begin
  induction t; intros; is_searchable_tactic,
  { cases lo; simp [lift, *] at *, apply lt_of_lt_of_incomp, assumption, exact ⟨hc.2, hc.1⟩ },
  all_goals { apply t_ih_rchild hc hs_hs₂ }
end

lemma is_searchable_of_incomp_of_is_searchable [is_strict_weak_order α lt] {t} : ∀ {lo lo' hi} (hc : ¬ lt lo' lo ∧ ¬ lt lo lo') (hs : is_searchable lt t (some lo) hi), is_searchable lt t (some lo') hi :=
begin
  induction t; intros; is_searchable_tactic,
  { cases hi; simp [lift, *] at *, apply lt_of_incomp_of_lt, assumption, assumption },
  all_goals { apply t_ih_lchild hc hs_hs₁ }
end

lemma is_searchable_some_low_of_is_searchable_of_lt {t} [is_trans α lt] : ∀ {lo hi lo'} (hlt : lt lo' lo) (hs : is_searchable lt t (some lo) hi), is_searchable lt t (some lo') hi :=
begin
  induction t; intros; is_searchable_tactic,
  { cases hi; simp [lift, *] at *, apply trans_of lt hlt, assumption },
  all_goals { apply t_ih_lchild hlt hs_hs₁ }
end

lemma is_searchable_none_low_of_is_searchable_some_low {t} : ∀ {y hi} (hlt : is_searchable lt t (some y) hi), is_searchable lt t none hi :=
begin
  induction t; intros; is_searchable_tactic,
  { simp [lift] },
  all_goals { apply t_ih_lchild hlt_hs₁ }
end

lemma is_searchable_some_high_of_is_searchable_of_lt {t} [is_trans α lt] : ∀ {lo hi hi'} (hlt : lt hi hi') (hs : is_searchable lt t lo (some hi)), is_searchable lt t lo (some hi') :=
begin
  induction t; intros; is_searchable_tactic,
  { cases lo; simp [lift, *] at *, apply trans_of lt, assumption, assumption},
  all_goals { apply t_ih_rchild hlt hs_hs₂ }
end

lemma is_searchable_none_high_of_is_searchable_some_high {t} : ∀ {lo y} (hlt : is_searchable lt t lo (some y)), is_searchable lt t lo none :=
begin
  induction t; intros; is_searchable_tactic,
  { cases lo; simp [lift] },
  all_goals { apply t_ih_rchild hlt_hs₂ }
end

lemma range [is_strict_weak_order α lt] {t : rbnode α} {x} : ∀ {lo hi}, is_searchable lt t lo hi → mem lt x t → lift lt lo (some x) ∧ lift lt (some x) hi :=
begin
  induction t,
  case leaf { simp [mem], intros, trivial },
  all_goals { -- red_node and black_node are identical
    intros lo hi h₁ h₂, cases h₁,
    simp only [mem] at h₂,
    have val_hi : lift lt (some t_val) hi, { apply lo_lt_hi, assumption },
    have lo_val : lift lt lo (some t_val), { apply lo_lt_hi, assumption },
    blast_disjs,
    {
      have h₃ : lift lt lo (some x) ∧ lift lt (some x) (some t_val), { apply t_ih_lchild, assumption, assumption },
      cases h₃ with lo_x x_val,
      split,
      show lift lt lo (some x), { assumption },
      show lift lt (some x ) hi, {
        cases hi with hi; simp [lift] at *,
        apply trans_of lt x_val val_hi
      }
    },
    {
      cases h₂,
      cases lo with lo; cases hi with hi; simp [lift] at *,
      { apply lt_of_incomp_of_lt _ val_hi, simp [*] },
      { apply lt_of_lt_of_incomp lo_val, simp [*] },
      split,
      { apply lt_of_lt_of_incomp lo_val, simp [*] },
      { apply lt_of_incomp_of_lt _ val_hi, simp [*] }
    },
    {
      have h₃ : lift lt (some t_val) (some x) ∧ lift lt (some x) hi, { apply t_ih_rchild, assumption, assumption },
      cases h₃ with val_x x_hi,
      cases lo with lo; cases hi with hi; simp [lift] at *,
      { assumption },
      { apply trans_of lt lo_val val_x },
      split,
      { apply trans_of lt lo_val val_x, },
      { assumption }
    }
  }
end

lemma lt_of_mem_left [is_strict_weak_order α lt] {y : α} {t l r : rbnode α} : ∀ {lo hi}, is_searchable lt t lo hi → is_node_of t l y r → ∀ {x}, mem lt x l → lt x y :=
begin
 intros _ _ hs hn x hm, cases hn; cases hs,
 all_goals { exact (range hs_hs₁ hm).2 }
end

lemma lt_of_mem_right [is_strict_weak_order α lt] {y : α} {t l r : rbnode α} : ∀ {lo hi}, is_searchable lt t lo hi → is_node_of t l y r → ∀ {z}, mem lt z r → lt y z :=
begin
 intros _ _ hs hn z hm, cases hn; cases hs,
 all_goals { exact (range hs_hs₂ hm).1 }
end

lemma lt_of_mem_left_right [is_strict_weak_order α lt] {y : α} {t l r : rbnode α} : ∀ {lo hi}, is_searchable lt t lo hi → is_node_of t l y r → ∀ {x z}, mem lt x l → mem lt z r → lt x z :=
begin
 intros _ _ hs hn x z hm₁ hm₂, cases hn; cases hs,
 all_goals {
   have h₁ := range hs_hs₁ hm₁,
   have h₂ := range hs_hs₂ hm₂,
   exact trans_of lt h₁.2 h₂.1,
 }
end

end is_searchable_lemmas

inductive is_red_black : rbnode α → color → nat → Prop
| leaf_rb  : is_red_black leaf black 0
| red_rb   {v l r n} (rb_l : is_red_black l black n) (rb_r : is_red_black r black n) : is_red_black (red_node l v r) red n
| black_rb {v l r n c₁ c₂} (rb_l : is_red_black l c₁ n) (rb_r : is_red_black r c₂ n) : is_red_black (black_node l v r) black (succ n)

open is_red_black

lemma depth_min : ∀ {c n} {t : rbnode α}, is_red_black t c n → depth min t ≥ n :=
begin
  intros c n' t h,
  induction h,
  case leaf_rb {apply le_refl},
  case red_rb { simp [depth],
    have : min (depth min h_l) (depth min h_r) ≥ h_n,
    { apply le_min; assumption },
    apply le_succ_of_le, assumption },
  case black_rb { simp [depth],
    apply succ_le_succ,
    apply le_min; assumption }
end

private def upper : color → nat → nat
| red   n := 2*n + 1
| black n := 2*n

private lemma upper_le : ∀ c n, upper c n ≤ 2 * n + 1
| red n   := by apply le_refl
| black n := by apply le_succ

lemma depth_max' : ∀ {c n} {t : rbnode α}, is_red_black t c n → depth max t ≤ upper c n :=
begin
  intros c n' t h,
  induction h,
  case leaf_rb { simp [max, depth, upper] },
  case red_rb {
    suffices : succ (max (depth max h_l) (depth max h_r)) ≤ 2 * h_n + 1,
    { simp [depth, upper, *] at * },
    apply succ_le_succ,
    apply max_le; assumption },
  case black_rb {
    have : depth max h_l ≤ 2*h_n + 1, from le_trans h_ih_rb_l (upper_le _ _),
    have : depth max h_r ≤ 2*h_n + 1, from le_trans h_ih_rb_r (upper_le _ _),
    suffices new : max (depth max h_l) (depth max h_r) + 1 ≤ 2 * h_n + 2*1,
    { simp [depth, upper, succ_eq_add_one, left_distrib, *] at * },
    apply succ_le_succ, apply max_le; assumption
  }
end

lemma depth_max {c n} {t : rbnode α} (h : is_red_black t c n) : depth max t ≤ 2 * n + 1:=
le_trans (depth_max' h) (upper_le _ _)

lemma balanced {c n} {t : rbnode α} (h : is_red_black t c n) : 2 * depth min t + 1 ≥ depth max t :=
begin
 have : 2 * depth min t + 1 ≥ 2 * n + 1,
 { apply succ_le_succ, apply mul_le_mul_left, apply depth_min h},
 apply le_trans, apply depth_max h, apply this
end

end rbnode
