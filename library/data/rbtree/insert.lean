/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.rbtree.find
universes u v

local attribute [simp] rbnode.lift

namespace rbnode
variables {α : Type u}

open color

@[simp] lemma balance1_eq₁ (l : rbnode α) (x r₁ y r₂ v t) : balance1 (red_node l x r₁) y r₂ v t = red_node (black_node l x r₁) y (black_node r₂ v t) :=
begin cases r₂; refl end

@[simp] lemma balance1_eq₂ (l₁ : rbnode α) (y l₂ x r v t) : get_color l₁ ≠ red → balance1 l₁ y (red_node l₂ x r)  v t = red_node (black_node l₁ y l₂) x (black_node r v t) :=
begin cases l₁; simp [get_color, balance1] end

@[simp] lemma balance1_eq₃ (l : rbnode α) (y r v t) : get_color l ≠ red → get_color r ≠ red → balance1 l y r v t = black_node (red_node l y r) v t :=
begin cases l; cases r; simp [get_color, balance1] end

@[simp] lemma balance2_eq₁ (l : rbnode α) (x₁ r₁ y r₂ v t) : balance2 (red_node l x₁ r₁) y r₂  v t = red_node (black_node t v l) x₁ (black_node r₁ y r₂) :=
by cases r₂; refl

@[simp] lemma balance2_eq₂ (l₁ : rbnode α) (y l₂ x₂ r₂ v t) : get_color l₁ ≠ red → balance2 l₁ y (red_node l₂ x₂ r₂) v t = red_node (black_node t v l₁) y (black_node l₂ x₂ r₂) :=
begin cases l₁; simp [get_color, balance2] end

@[simp] lemma balance2_eq₃ (l : rbnode α) (y r v t) : get_color l ≠ red → get_color r ≠ red → balance2 l  y r  v t = black_node t v (red_node l y r) :=
begin cases l; cases r; simp [get_color, balance2] end

/- We can use the same induction principle for balance1 and balance2 -/
lemma balance.cases {p : rbnode α → α → rbnode α → Prop}
  (l y r)
  (red_left : ∀ l x r₁ y r₂, p (red_node l x r₁) y r₂)
  (red_right : ∀ l₁ y l₂ x r, get_color l₁ ≠ red → p l₁ y (red_node l₂ x r))
  (other : ∀ l y r, get_color l ≠ red → get_color r ≠ red → p l y r)
  : p l y r :=
begin
  cases l; cases r,
  any_goals { apply red_left },
  any_goals { apply red_right; simp [get_color]; contradiction; done },
  any_goals { apply other; simp [get_color]; contradiction; done },
end

lemma balance1_ne_leaf (l : rbnode α) (x r v t) : balance1 l x r v t ≠ leaf :=
by apply balance.cases l x r; intros; simp [*]; contradiction

lemma balance1_node_ne_leaf {s : rbnode α} (a : α) (t : rbnode α) : s ≠ leaf → balance1_node s a t ≠ leaf :=
begin
  intro h, cases s,
  { contradiction },
  all_goals { simp [balance1_node], apply balance1_ne_leaf }
end

lemma balance2_ne_leaf (l : rbnode α) (x r v t) : balance2 l x r v t ≠ leaf :=
by apply balance.cases l x r; intros; simp [*]; contradiction

lemma balance2_node_ne_leaf {s : rbnode α} (a : α) (t : rbnode α) : s ≠ leaf → balance2_node s a t ≠ leaf :=
begin
  intro h, cases s,
  { contradiction },
  all_goals { simp [balance2_node], apply balance2_ne_leaf }
end

variables (lt : α → α → Prop) [decidable_rel lt]

@[elab_as_eliminator]
lemma ins.induction {p : rbnode α → Prop}
  (t x)
  (is_leaf : p leaf)
  (is_red_lt : ∀ a y b (hc : cmp_using lt x y = ordering.lt) (ih : p a), p (red_node a y b))
  (is_red_eq : ∀ a y b (hc : cmp_using lt x y = ordering.eq), p (red_node a y b))
  (is_red_gt : ∀ a y b (hc : cmp_using lt x y = ordering.gt) (ih : p b), p (red_node a y b))
  (is_black_lt_red : ∀ a y b (hc : cmp_using lt x y = ordering.lt) (hr : get_color a = red) (ih : p a), p (black_node a y b))
  (is_black_lt_not_red : ∀ a y b (hc : cmp_using lt x y = ordering.lt) (hnr : get_color a ≠ red) (ih : p a), p (black_node a y b))
  (is_black_eq : ∀ a y b (hc : cmp_using lt x y = ordering.eq), p (black_node a y b))
  (is_black_gt_red : ∀ a y b (hc : cmp_using lt x y = ordering.gt) (hr : get_color b = red) (ih : p b), p (black_node a y b))
  (is_black_gt_not_red : ∀ a y b (hc : cmp_using lt x y = ordering.gt) (hnr : get_color b ≠ red) (ih : p b), p (black_node a y b))
  : p t :=
begin
  induction t,
  case leaf { apply is_leaf },
  case red_node : a y b {
     cases h : cmp_using lt x y,
     case ordering.lt { apply is_red_lt; assumption },
     case ordering.eq { apply is_red_eq; assumption },
     case ordering.gt { apply is_red_gt; assumption },
   },
  case black_node : a y b {
     cases h : cmp_using lt x y,
     case ordering.lt {
       by_cases get_color a = red,
       { apply is_black_lt_red; assumption },
       { apply is_black_lt_not_red; assumption },
     },
     case ordering.eq { apply is_black_eq; assumption },
     case ordering.gt {
       by_cases get_color b = red,
       { apply is_black_gt_red; assumption },
       { apply is_black_gt_not_red; assumption },
     }
  }
end

lemma is_searchable_balance1 {l y r v t lo hi} : is_searchable lt l lo (some y) →  is_searchable lt r (some y) (some v) → is_searchable lt t (some v) hi → is_searchable lt (balance1 l y r v t) lo hi :=
by apply balance.cases l y r; intros; simp [*]; is_searchable_tactic

lemma is_searchable_balance1_node {t} [is_trans α lt] : ∀ {y s lo hi}, is_searchable lt t lo (some y) → is_searchable lt s (some y) hi → is_searchable lt (balance1_node t y s) lo hi :=
begin
  cases t; simp!; intros; is_searchable_tactic,
  { cases lo,
    { apply is_searchable_none_low_of_is_searchable_some_low, assumption },
    { simp at *, apply is_searchable_some_low_of_is_searchable_of_lt; assumption } },
  all_goals { apply is_searchable_balance1; assumption }
end

lemma is_searchable_balance2 {l y r v t lo hi} : is_searchable lt t lo (some v) → is_searchable lt l (some v) (some y) → is_searchable lt r (some y) hi → is_searchable lt (balance2 l y r v t) lo hi :=
by apply balance.cases l y r; intros; simp [*]; is_searchable_tactic

lemma is_searchable_balance2_node {t} [is_trans α lt] : ∀ {y s lo hi}, is_searchable lt s lo (some y) → is_searchable lt t (some y) hi → is_searchable lt (balance2_node t y s) lo hi :=
begin
  induction t; simp!; intros; is_searchable_tactic,
  { cases hi,
    { apply is_searchable_none_high_of_is_searchable_some_high, assumption },
    { simp at *, apply is_searchable_some_high_of_is_searchable_of_lt, assumption' } },
  all_goals { apply is_searchable_balance2, assumption' }
end

lemma is_searchable_ins {t x} [is_strict_weak_order α lt] : ∀ {lo hi} (h : is_searchable lt t lo hi), lift lt lo (some x) → lift lt (some x) hi → is_searchable lt (ins lt t x) lo hi :=
begin
  with_cases { apply ins.induction lt t x; intros; simp! [*] at * {eta := ff}; is_searchable_tactic },
  case is_red_lt { apply ih h_hs₁, assumption, simp [*] },
  case is_red_eq hs₁ { apply is_searchable_of_is_searchable_of_incomp hc, assumption },
  case is_red_eq hs₂ { apply is_searchable_of_incomp_of_is_searchable hc, assumption },
  case is_red_gt { apply ih h_hs₂, cases hi; simp [*], assumption },
  case is_black_lt_red { apply is_searchable_balance1_node, apply ih h_hs₁, assumption, simp [*], assumption },
  case is_black_lt_not_red { apply ih h_hs₁, assumption, simp [*] },
  case is_black_eq hs₁ { apply is_searchable_of_is_searchable_of_incomp hc, assumption },
  case is_black_eq hs₂ { apply is_searchable_of_incomp_of_is_searchable hc, assumption },
  case is_black_gt_red { apply is_searchable_balance2_node, assumption, apply ih h_hs₂, simp [*], assumption },
  case is_black_gt_not_red { apply ih h_hs₂, assumption, simp [*] }
end

lemma is_searchable_mk_insert_result {c t} : is_searchable lt t none none → is_searchable lt (mk_insert_result c t) none none :=
begin
  cases c; cases t; simp [mk_insert_result],
  any_goals { exact id },
  { intro h, is_searchable_tactic }
end

lemma is_searchable_insert {t x} [is_strict_weak_order α lt] : is_searchable lt t none none → is_searchable lt (insert lt t x) none none :=
begin
  intro h, simp [insert], apply is_searchable_mk_insert_result, apply is_searchable_ins; { assumption <|> simp }
end

end rbnode

namespace rbnode
section membership_lemmas
parameters {α : Type u} (lt : α → α → Prop) [decidable_rel lt]

local attribute [simp] mem balance1_node balance2_node

local infix `∈` := mem lt

lemma mem_balance1_node_of_mem_left {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance1_node s v t :=
begin
  cases s; simp,
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp at *; blast_disjs; simp [*] }
end

lemma mem_balance2_node_of_mem_left {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance2_node s v t :=
begin
  cases s; simp,
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp at *; blast_disjs; simp [*] }
end

lemma mem_balance1_node_of_mem_right {x t} (v) (s : rbnode α) : x ∈ t → x ∈ balance1_node s v t :=
begin
  intros, cases s; simp [*],
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp [*] }
end

lemma mem_balance2_node_of_mem_right {x t} (v) (s : rbnode α) : x ∈ t → x ∈ balance2_node s v t :=
begin
  intros, cases s; simp [*],
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp [*] }
end

lemma mem_balance1_node_of_incomp {x v} (s t) : (¬ lt x v ∧ ¬ lt v x) → s ≠ leaf → x ∈ balance1_node s v t :=
begin
  intros, cases s; simp,
  { contradiction },
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp [*] }
end

lemma mem_balance2_node_of_incomp {x v} (s t) : (¬ lt v x ∧ ¬ lt x v) → s ≠ leaf → x ∈ balance2_node s v t :=
begin
  intros, cases s; simp,
  { contradiction },
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp [*] }
end

lemma ins_ne_leaf (t : rbnode α) (x : α) : t.ins lt x ≠ leaf :=
begin
  apply ins.induction lt t x,
  any_goals { intros, simp [ins, *] },
  { intros, apply balance1_node_ne_leaf, assumption },
  { intros, apply balance2_node_ne_leaf, assumption },
end

lemma insert_ne_leaf (t : rbnode α) (x : α) : insert lt t x ≠ leaf :=
begin
  simp [insert],
  cases he : ins lt t x; cases get_color t; simp [mk_insert_result],
  { have := ins_ne_leaf lt t x, contradiction },
  { exact absurd he (ins_ne_leaf _ _ _) }
end

lemma mem_ins_of_incomp (t : rbnode α) {x y : α} : ∀ h : ¬ lt x y ∧ ¬ lt y x, x ∈ t.ins lt y :=
begin
  with_cases { apply ins.induction lt t y; intros; simp [ins, *] },
  case is_black_lt_red { have := ih h, apply mem_balance1_node_of_mem_left, assumption },
  case is_black_gt_red { have := ih h, apply mem_balance2_node_of_mem_left, assumption }
end

lemma mem_ins_of_mem [is_strict_weak_order α lt] {t : rbnode α} (z : α) : ∀ {x} (h : x ∈ t), x ∈ t.ins lt z :=
begin
  with_cases { apply ins.induction lt t z; intros; simp [ins, *] at *; try { contradiction }; blast_disjs },
  case is_red_eq or.inr or.inl {
    have := incomp_trans_of lt h ⟨hc.2, hc.1⟩, simp [this] },
  case is_black_lt_red or.inl {
    apply mem_balance1_node_of_mem_left, apply ih h },
  case is_black_lt_red or.inr or.inl {
    have := ins_ne_leaf lt a z, apply mem_balance1_node_of_incomp, cases h, all_goals { simp [*] } },
  case is_black_lt_red or.inr or.inr {
    apply mem_balance1_node_of_mem_right, assumption },
  case is_black_eq or.inr or.inl {
    have := incomp_trans_of lt hc ⟨h.2, h.1⟩, simp [this] },
  case is_black_gt_red or.inl {
    apply mem_balance2_node_of_mem_right, assumption },
  case is_black_gt_red or.inr or.inl {
    have := ins_ne_leaf lt a z, apply mem_balance2_node_of_incomp, cases h, simp [*], apply ins_ne_leaf },
  case is_black_gt_red or.inr or.inr {
    apply mem_balance2_node_of_mem_left, apply ih h },
  -- remaining cases are easy
  any_goals { intros, simp [h], done },
  all_goals { intros, simp [ih h], done },
end

lemma mem_mk_insert_result {a t} (c) : mem lt a t → mem lt a (mk_insert_result c t) :=
by intros; cases c; cases t; simp [mk_insert_result, mem, *] at *

lemma mem_of_mem_mk_insert_result {a t c} : mem lt a (mk_insert_result c t) → mem lt a t :=
by cases t; cases c; simp [mk_insert_result, mem]; intros; assumption

lemma mem_insert_of_incomp (t : rbnode α) {x y : α} : ∀ h : ¬ lt x y ∧ ¬ lt y x, x ∈ t.insert lt y :=
by intros; unfold insert; apply mem_mk_insert_result; apply mem_ins_of_incomp; assumption

lemma mem_insert_of_mem [is_strict_weak_order α lt] {t x} (z) : x ∈ t → x ∈ t.insert lt z :=
by intros; apply mem_mk_insert_result; apply mem_ins_of_mem; assumption

lemma of_mem_balance1_node [is_strict_weak_order α lt] {x s v t} : x ∈ balance1_node s v t → x ∈ s ∨ (¬ lt x v ∧ ¬ lt v x) ∨ x ∈ t :=
begin
  cases s; simp,
  { intros, simp [*] },
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp [*] at *; blast_disjs; simp [*] }
end

lemma of_mem_balance2_node [is_strict_weak_order α lt] {x s v t} : x ∈ balance2_node s v t → x ∈ s ∨ (¬ lt x v ∧ ¬ lt v x) ∨ x ∈ t :=
begin
  cases s; simp,
  { intros, simp [*] },
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp [*] at *; blast_disjs; simp [*] }
end

lemma equiv_or_mem_of_mem_ins [is_strict_weak_order α lt] {t : rbnode α} {x z} : ∀ (h : x ∈ t.ins lt z), x ≈[lt] z ∨ x ∈ t :=
begin
  with_cases { apply ins.induction lt t z; intros; simp [ins, strict_weak_order.equiv, *] at *; blast_disjs },
  case is_black_lt_red {
     have h' := of_mem_balance1_node lt h, blast_disjs,
     have := ih h', blast_disjs,
     all_goals { simp [h, *] } },
  case is_black_gt_red {
     have h' := of_mem_balance2_node lt h, blast_disjs,
     have := ih h', blast_disjs,
     all_goals { simp [h, *] }},
  -- All other goals can be solved by the following tactics
  any_goals { intros, simp [h] },
  all_goals { intros, have ih := ih h, cases ih; simp [*], done },
end

lemma equiv_or_mem_of_mem_insert [is_strict_weak_order α lt] {t : rbnode α} {x z} : ∀ (h : x ∈ t.insert lt z), x ≈[lt] z ∨ x ∈ t :=
begin
  simp [insert], intros, apply equiv_or_mem_of_mem_ins, exact mem_of_mem_mk_insert_result lt h
end

local attribute [simp] mem_exact

lemma mem_exact_balance1_node_of_mem_exact {x s} (v) (t : rbnode α) : mem_exact x s → mem_exact x (balance1_node s v t) :=
begin
  cases s; simp,
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp [*] at *; blast_disjs; simp [*] }
end

lemma mem_exact_balance2_node_of_mem_exact {x s} (v) (t : rbnode α) : mem_exact x s → mem_exact x (balance2_node s v t) :=
begin
  cases s; simp,
  all_goals { apply balance.cases s_lchild s_val s_rchild; intros; simp [*] at *; blast_disjs; simp [*] }
end

lemma find_balance1_node [is_strict_weak_order α lt] {x y z t s} : ∀ {lo hi}, is_searchable lt t lo (some z) → is_searchable lt s (some z) hi → find lt t y = some x → y ≈[lt] x → find lt (balance1_node t z s) y = some x :=
begin
  intros _ _ hs₁ hs₂ heq heqv,
  have hs := is_searchable_balance1_node lt hs₁ hs₂,
  have := eq.trans (find_eq_find_of_eqv hs₁ heqv.symm) heq,
  have := iff.mpr (find_correct_exact hs₁) this,
  have := mem_exact_balance1_node_of_mem_exact z s this,
  have := iff.mp (find_correct_exact hs) this,
  exact eq.trans (find_eq_find_of_eqv hs heqv) this
end

lemma find_balance2_node [is_strict_weak_order α lt] {x y z s t} [is_trans α lt] : ∀ {lo hi}, is_searchable lt s lo (some z) → is_searchable lt t (some z) hi → find lt t y = some x → y ≈[lt] x → find lt (balance2_node t z s) y = some x :=
begin
  intros _ _ hs₁ hs₂ heq heqv,
  have hs := is_searchable_balance2_node lt hs₁ hs₂,
  have := eq.trans (find_eq_find_of_eqv hs₂ heqv.symm) heq,
  have := iff.mpr (find_correct_exact hs₂) this,
  have := mem_exact_balance2_node_of_mem_exact z s this,
  have := iff.mp (find_correct_exact hs) this,
  exact eq.trans (find_eq_find_of_eqv hs heqv) this
end

/- Auxiliary lemma -/

lemma ite_eq_of_not_lt [is_strict_order α lt] {a b} {β : Type v} (t s : β) (h : lt b a) : (if lt a b then t else s) = s :=
begin have := not_lt_of_lt h, simp [*] end

local attribute [simp] ite_eq_of_not_lt

private meta def simp_fi : tactic unit :=
`[simp [find, ins, *, cmp_using]]

lemma find_ins_of_eqv [is_strict_weak_order α lt] {x y : α} {t : rbnode α} (he : x ≈[lt] y) : ∀ {lo hi} (hs : is_searchable lt t lo hi) (hlt₁ : lift lt lo (some x)) (hlt₂ : lift lt (some x) hi), find lt (ins lt t x) y = some x :=
begin
  simp [strict_weak_order.equiv] at he,
  apply ins.induction lt t x; intros,
  { simp_fi },
  all_goals { simp at hc, cases hs },
  { have := lt_of_incomp_of_lt he.swap hc,
    have := ih hs_hs₁ hlt₁ hc,
    simp_fi },
  { simp_fi },
  { have := lt_of_lt_of_incomp hc he,
    have := ih hs_hs₂ hc hlt₂,
    simp_fi },
  { simp_fi,
    have := is_searchable_ins lt hs_hs₁ hlt₁ hc,
    apply find_balance1_node lt this hs_hs₂ (ih hs_hs₁ hlt₁ hc) he.symm },
  { have := lt_of_incomp_of_lt he.swap hc,
    have := ih hs_hs₁ hlt₁ hc,
    simp_fi },
  { simp_fi },
  { simp_fi,
    have := is_searchable_ins lt hs_hs₂ hc hlt₂,
    apply find_balance2_node lt hs_hs₁ this (ih hs_hs₂ hc hlt₂) he.symm },
  { have := lt_of_lt_of_incomp hc he,
    have := ih hs_hs₂ hc hlt₂,
    simp_fi }
end

lemma find_mk_insert_result (c : color) (t : rbnode α) (x : α) : find lt (mk_insert_result c t) x = find lt t x :=
begin
  cases t; cases c; simp [mk_insert_result],
  { simp [find], cases cmp_using lt x t_val; simp [find] }
end

lemma find_insert_of_eqv [is_strict_weak_order α lt] {x y : α} {t : rbnode α} (he : x ≈[lt] y) : is_searchable lt t none none → find lt (insert lt t x) y = some x :=
begin
  intro hs,
  simp [insert, find_mk_insert_result],
  apply find_ins_of_eqv lt he hs; simp
end

lemma weak_trichotomous (x y) {p : Prop} (is_lt : ∀ h : lt x y, p) (is_eqv : ∀ h : ¬ lt x y ∧ ¬ lt y x, p) (is_gt : ∀ h : lt y x, p) : p :=
begin
  by_cases lt x y; by_cases lt y x,
  any_goals { apply is_lt; assumption },
  any_goals { apply is_gt; assumption },
  any_goals { apply is_eqv, constructor; assumption }
end

section find_ins_of_not_eqv

section simp_aux_lemmas

lemma find_black_eq_find_red {l y r x} : find lt (black_node l y r) x = find lt (red_node l y r) x :=
begin simp [find], all_goals { cases cmp_using lt x y; simp [find] } end

lemma find_red_of_lt {l y r x} (h : lt x y) : find lt (red_node l y r) x = find lt l x :=
by simp [find, cmp_using, *]

lemma find_red_of_gt [is_strict_order α lt] {l y r x} (h : lt y x) : find lt (red_node l y r) x = find lt r x :=
begin have := not_lt_of_lt h, simp [find, cmp_using, *]  end

lemma find_red_of_incomp {l y r x} (h : ¬ lt x y ∧ ¬ lt y x) : find lt (red_node l y r) x = some y :=
by simp [find, cmp_using, *]

end simp_aux_lemmas

local attribute [simp]
  find_black_eq_find_red find_red_of_lt find_red_of_lt find_red_of_gt
  find_red_of_incomp

variable [is_strict_weak_order α lt]

lemma find_balance1_lt {l r t v x y lo hi}
                       (h : lt x y)
                       (hl : is_searchable lt l lo (some v))
                       (hr : is_searchable lt r (some v) (some y))
                       (ht : is_searchable lt t (some y) hi)
                       : find lt (balance1 l v r y t) x = find lt (red_node l v r) x :=
begin
  with_cases { revert hl hr ht, apply balance.cases l v r; intros; simp [*]; is_searchable_tactic },
  case red_left : _ _ _ z r { apply weak_trichotomous lt z x; intros; simp [*] },
  case red_right : l_left l_val l_right z r {
    with_cases { apply weak_trichotomous lt z x; intro h' },
    case is_lt  { have := trans_of lt (lo_lt_hi hr_hs₁) h', simp [*] },
    case is_eqv { have : lt l_val x := lt_of_lt_of_incomp (lo_lt_hi hr_hs₁) h', simp [*] },
    case is_gt  { apply weak_trichotomous lt l_val x; intros; simp [*] } }
end

meta def ins_ne_leaf_tac := `[apply ins_ne_leaf]

lemma find_balance1_node_lt {t s x y lo hi} (hlt : lt y x)
                            (ht : is_searchable lt t lo (some x))
                            (hs : is_searchable lt s (some x) hi)
                            (hne : t ≠ leaf . ins_ne_leaf_tac)
                            : find lt (balance1_node t x s) y = find lt t y :=
begin
  cases t; simp [balance1_node],
  { contradiction },
  all_goals { intros, is_searchable_tactic, apply find_balance1_lt, assumption' }
end

lemma find_balance1_gt {l r t v x y lo hi}
                       (h : lt y x)
                       (hl : is_searchable lt l lo (some v))
                       (hr : is_searchable lt r (some v) (some y))
                       (ht : is_searchable lt t (some y) hi)
                       : find lt (balance1 l v r y t) x = find lt t x :=
begin
  with_cases { revert hl hr ht, apply balance.cases l v r; intros; simp [*]; is_searchable_tactic },
  case red_left : _ _ _ z {
    have := trans_of lt (lo_lt_hi hr) h, simp [*] },
  case red_right : _ _ _ z {
    have := trans_of lt (lo_lt_hi hr_hs₂) h, simp [*] }
end

lemma find_balance1_node_gt {t s x y lo hi} (h : lt x y)
                            (ht : is_searchable lt t lo (some x))
                            (hs : is_searchable lt s (some x) hi)
                            (hne : t ≠ leaf . ins_ne_leaf_tac)
                            : find lt (balance1_node t x s) y = find lt s y :=
begin
  cases t; simp [balance1_node],
  all_goals { intros, is_searchable_tactic, apply find_balance1_gt, assumption' }
end

lemma find_balance1_eqv {l r t v x y lo hi}
                        (h : ¬ lt x y ∧ ¬ lt y x)
                        (hl : is_searchable lt l lo (some v))
                        (hr : is_searchable lt r (some v) (some y))
                        (ht : is_searchable lt t (some y) hi)
                        : find lt (balance1 l v r y t) x = some y :=
begin
  with_cases { revert hl hr ht, apply balance.cases l v r; intros; simp [*]; is_searchable_tactic },
  case red_left : _ _ _ z {
    have : lt z x := lt_of_lt_of_incomp (lo_lt_hi hr) h.swap,
    simp [*] },
  case red_right : _ _ _ z {
    have : lt z x := lt_of_lt_of_incomp (lo_lt_hi hr_hs₂) h.swap,
    simp [*] }
end

lemma find_balance1_node_eqv {t s x y lo hi}
                             (h : ¬ lt x y ∧ ¬ lt y x)
                             (ht : is_searchable lt t lo (some y))
                             (hs : is_searchable lt s (some y) hi)
                             (hne : t ≠ leaf . ins_ne_leaf_tac)
                             : find lt (balance1_node t y s) x = some y :=
begin
  cases t; simp [balance1_node],
  { contradiction },
  all_goals { intros, is_searchable_tactic, apply find_balance1_eqv, assumption' }
end

lemma find_balance2_lt {l v r t x y lo hi}
                       (h :  lt x y)
                       (hl : is_searchable lt l (some y) (some v))
                       (hr : is_searchable lt r (some v) hi)
                       (ht : is_searchable lt t lo (some y))
                       : find lt (balance2 l v r y t) x = find lt t x :=
begin
  with_cases { revert hl hr ht, apply balance.cases l v r; intros; simp [*]; is_searchable_tactic },
  case red_left { have := trans h (lo_lt_hi hl_hs₁), simp [*] },
  case red_right { have := trans h (lo_lt_hi hl), simp [*] }
end

lemma find_balance2_node_lt {s t x y lo hi}
                            (h : lt x y)
                            (ht : is_searchable lt t (some y) hi)
                            (hs : is_searchable lt s lo (some y))
                            (hne : t ≠ leaf . ins_ne_leaf_tac)
                            : find lt (balance2_node t y s) x = find lt s x :=
begin
  cases t; simp [balance2_node],
  all_goals { intros, is_searchable_tactic, apply find_balance2_lt, assumption' }
end

lemma find_balance2_gt {l v r t x y lo hi}
                       (h :  lt y x)
                       (hl : is_searchable lt l (some y) (some v))
                       (hr : is_searchable lt r (some v) hi)
                       (ht : is_searchable lt t lo (some y))
                       : find lt (balance2 l v r y t) x = find lt (red_node l v r) x :=
begin
  with_cases { revert hl hr ht, apply balance.cases l v r; intros; simp [*]; is_searchable_tactic },
  case red_left : _ val _ z {
    with_cases { apply weak_trichotomous lt val x; intro h'; simp [*] },
    case is_lt { apply weak_trichotomous lt z x; intros; simp [*] },
    case is_eqv { have : lt x z := lt_of_incomp_of_lt h'.swap (lo_lt_hi hl_hs₂), simp [*] },
    case is_gt  { have := trans h' (lo_lt_hi hl_hs₂), simp [*] } },
  case red_right : _ val {
    apply weak_trichotomous lt val x; intros; simp [*] }
end

lemma find_balance2_node_gt {s t x y lo hi}
                            (h : lt y x)
                            (ht : is_searchable lt t (some y) hi)
                            (hs : is_searchable lt s lo (some y))
                            (hne : t ≠ leaf . ins_ne_leaf_tac)
                            : find lt (balance2_node t y s) x = find lt t x :=
begin
  cases t; simp [balance2_node],
  { contradiction },
  all_goals { intros, is_searchable_tactic, apply find_balance2_gt, assumption' }
end

lemma find_balance2_eqv {l v r t x y lo hi}
                        (h : ¬ lt x y ∧ ¬ lt y x)
                        (hl : is_searchable lt l (some y) (some v))
                        (hr : is_searchable lt r (some v) hi)
                        (ht : is_searchable lt t lo (some y))
                        : find lt (balance2 l v r y t) x = some y :=
begin
  with_cases { revert hl hr ht, apply balance.cases l v r; intros; simp [*]; is_searchable_tactic },
  case red_left { have := lt_of_incomp_of_lt h (lo_lt_hi hl_hs₁), simp [*] },
  case red_right { have := lt_of_incomp_of_lt h (lo_lt_hi hl), simp [*] }
end

lemma find_balance2_node_eqv {t s x y lo hi}
                             (h : ¬ lt x y ∧ ¬ lt y x)
                             (ht : is_searchable lt t (some y) hi)
                             (hs : is_searchable lt s lo (some y))
                             (hne : t ≠ leaf . ins_ne_leaf_tac)
                             : find lt (balance2_node t y s) x = some y :=
begin
  cases t; simp [balance2_node],
  { contradiction },
  all_goals { intros, is_searchable_tactic, apply find_balance2_eqv, assumption' }
end

lemma find_ins_of_disj {x y : α} {t : rbnode α} (hn : lt x y ∨ lt y x)
                       : ∀ {lo hi}
                           (hs : is_searchable lt t lo hi)
                           (hlt₁ : lift lt lo (some x))
                           (hlt₂ : lift lt (some x) hi),
                           find lt (ins lt t x) y = find lt t y :=
begin
  apply ins.induction lt t x; intros,
  { cases hn,
    all_goals { simp [find, ins, cmp_using, *] } },
  all_goals { simp at hc, cases hs },
  { have := ih hs_hs₁ hlt₁ hc, simp_fi },
  { cases hn,
    { have := lt_of_incomp_of_lt hc.symm hn,
      simp_fi },
    { have := lt_of_lt_of_incomp hn hc,
      simp_fi } },
  { have := ih hs_hs₂ hc hlt₂,
    cases hn,
    { have := trans hc hn, simp_fi },
    { simp_fi } },
  { have ih := ih hs_hs₁ hlt₁ hc,
    cases hn,
    { cases hc' : cmp_using lt y y_1; simp at hc',
      { have hsi := is_searchable_ins lt hs_hs₁ hlt₁ (trans_of lt hn hc'),
        have := find_balance1_node_lt lt hc' hsi hs_hs₂,
        simp_fi },
      { have hlt := lt_of_lt_of_incomp hn hc',
        have hsi := is_searchable_ins lt hs_hs₁ hlt₁ hlt,
        have := find_balance1_node_eqv lt hc' hsi hs_hs₂,
        simp_fi },
      { have hsi := is_searchable_ins lt hs_hs₁ hlt₁ hc,
        have := find_balance1_node_gt lt hc' hsi hs_hs₂,
        simp [*], simp_fi } },
    { have hlt := trans hn hc,
      have hsi := is_searchable_ins lt hs_hs₁ hlt₁ hc,
      have := find_balance1_node_lt lt hlt hsi hs_hs₂,
      simp_fi } },
  { have := ih hs_hs₁ hlt₁ hc, simp_fi },
  { cases hn,
    { have := lt_of_incomp_of_lt hc.swap hn, simp_fi },
    { have := lt_of_lt_of_incomp hn hc, simp_fi } },
  { have ih := ih hs_hs₂ hc hlt₂,
    cases hn,
    { have hlt := trans hc hn, simp_fi,
      have hsi := is_searchable_ins lt hs_hs₂ hc hlt₂,
      have := find_balance2_node_gt lt hlt hsi hs_hs₁,
      simp_fi },
    { simp_fi,
      cases hc' : cmp_using lt y y_1; simp at hc',
      { have hsi := is_searchable_ins lt hs_hs₂ hc hlt₂,
        have := find_balance2_node_lt lt hc' hsi hs_hs₁,
        simp_fi },
      { have hlt := lt_of_incomp_of_lt hc'.swap hn,
        have hsi := is_searchable_ins lt hs_hs₂ hlt hlt₂,
        have := find_balance2_node_eqv lt hc' hsi hs_hs₁,
        simp_fi },
      { have hsi := is_searchable_ins lt hs_hs₂ hc hlt₂,
        have := find_balance2_node_gt lt hc' hsi hs_hs₁,
        simp_fi } } },
  { cases hn,
    { have := trans hc hn,
      have := ih hs_hs₂ hc hlt₂,
      simp_fi },
    { have ih := ih hs_hs₂ hc hlt₂,
      simp_fi } }
end

end find_ins_of_not_eqv

lemma find_insert_of_disj [is_strict_weak_order α lt] {x y : α} {t : rbnode α} (hd : lt x y ∨ lt y x) : is_searchable lt t none none → find lt (insert lt t x) y = find lt t y :=
begin
  intro hs,
  simp [insert, find_mk_insert_result],
  apply find_ins_of_disj lt hd hs; simp
end

lemma find_insert_of_not_eqv [is_strict_weak_order α lt] {x y : α} {t : rbnode α} (hn : ¬ x ≈[lt] y) : is_searchable lt t none none → find lt (insert lt t x) y = find lt t y :=
begin
  intro hs,
  simp [insert, find_mk_insert_result],
  have he : lt x y ∨ lt y x, {
    simp [strict_weak_order.equiv, decidable.not_and_iff_or_not, decidable.not_not_iff] at hn,
    assumption },
  apply find_ins_of_disj lt he hs; simp
end

end membership_lemmas

section is_red_black
variables {α : Type u}
open nat color

inductive is_bad_red_black : rbnode α → nat → Prop
| bad_red   {c₁ c₂ n l r v} (rb_l : is_red_black l c₁ n) (rb_r : is_red_black r c₂ n) : is_bad_red_black (red_node l v r) n

lemma balance1_rb {l r t : rbnode α} {y v : α} {c_l c_r c_t n} : is_red_black l c_l n → is_red_black r c_r n → is_red_black t c_t n → ∃ c, is_red_black (balance1 l y r v t) c (succ n) :=
by intros h₁ h₂ _; cases h₁; cases h₂; repeat { assumption <|> constructor }

lemma balance2_rb {l r t : rbnode α} {y v : α} {c_l c_r c_t n} : is_red_black l c_l n → is_red_black r c_r n → is_red_black t c_t n → ∃ c, is_red_black (balance2 l y r v t) c (succ n) :=
by intros h₁ h₂ _; cases h₁; cases h₂; repeat { assumption <|> constructor }

lemma balance1_node_rb {t s : rbnode α} {y : α} {c n} : is_bad_red_black t n → is_red_black s c n → ∃ c, is_red_black (balance1_node t y s) c (succ n) :=
by intros h _; cases h; simp [balance1_node]; apply balance1_rb; assumption'

lemma balance2_node_rb {t s : rbnode α} {y : α} {c n} : is_bad_red_black t n → is_red_black s c n → ∃ c, is_red_black (balance2_node t y s) c (succ n) :=
by intros h _; cases h; simp [balance2_node]; apply balance2_rb; assumption'

def ins_rb_result : rbnode α → color → nat → Prop
| t red   n := is_bad_red_black t n
| t black n := ∃ c, is_red_black t c n

variables {lt : α → α → Prop} [decidable_rel lt]

lemma of_get_color_eq_red {t : rbnode α} {c n} : get_color t = red → is_red_black t c n → c = red :=
begin intros h₁ h₂, cases h₂; simp [get_color] at h₁; contradiction end

lemma of_get_color_ne_red {t : rbnode α} {c n} : get_color t ≠ red → is_red_black t c n → c = black :=
begin intros h₁ h₂, cases h₂; simp [get_color] at h₁; contradiction end

variable (lt)

lemma ins_rb {t : rbnode α} (x) : ∀ {c n} (h : is_red_black t c n), ins_rb_result (ins lt t x) c n :=
begin
  apply ins.induction lt t x; intros; cases h; simp [ins, *, ins_rb_result],
  { repeat { constructor } },
  { specialize ih h_rb_l, cases ih, constructor; assumption },
  { constructor; assumption },
  { specialize ih h_rb_r, cases ih, constructor; assumption },
  { specialize ih h_rb_l,
    have := of_get_color_eq_red hr h_rb_l, subst h_c₁,
    simp [ins_rb_result] at ih,
    apply balance1_node_rb; assumption },
  { specialize ih h_rb_l,
    have := of_get_color_ne_red hnr h_rb_l, subst h_c₁,
    simp [ins_rb_result] at ih, cases ih,
    constructor, constructor; assumption },
  { constructor, constructor; assumption },
  { specialize ih h_rb_r,
    have := of_get_color_eq_red hr h_rb_r, subst h_c₂,
    simp [ins_rb_result] at ih,
    apply balance2_node_rb; assumption },
  { specialize ih h_rb_r,
    have := of_get_color_ne_red hnr h_rb_r, subst h_c₂,
    simp [ins_rb_result] at ih, cases ih,
    constructor, constructor; assumption }
end

def insert_rb_result : rbnode α → color → nat → Prop
| t red n   := is_red_black t black (succ n)
| t black n := ∃ c, is_red_black t c n

lemma insert_rb {t : rbnode α} (x) {c n} (h : is_red_black t c n) : insert_rb_result (insert lt t x) c n :=
begin
  simp [insert],
  have hi := ins_rb lt x h,
  generalize he : ins lt t x = r,
  simp [he] at hi,
  cases h; simp [get_color, ins_rb_result, insert_rb_result, mk_insert_result] at *,
  assumption',
  { cases hi, simp [mk_insert_result], constructor; assumption }
end

lemma insert_is_red_black {t : rbnode α} {c n} (x) : is_red_black t c n → ∃ c n, is_red_black (insert lt t x) c n :=
begin
  intro h,
  have := insert_rb lt x h,
  cases c; simp [insert_rb_result] at this,
  { constructor, constructor, assumption },
  { cases this, constructor, constructor, assumption }
end

end is_red_black

end rbnode
