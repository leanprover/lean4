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

lemma balance1_ne_leaf (l : rbnode α) (x r v t) : balance1 l x r v t ≠ leaf :=
by cases l; cases r; simp [balance1]; intro; contradiction

lemma balance1_node_ne_leaf {s : rbnode α} (a : α) (t : rbnode α) : s ≠ leaf → balance1_node s a t ≠ leaf :=
begin
  intro h, cases s,
  { contradiction },
  all_goals { simp [balance1_node], apply balance1_ne_leaf }
end

lemma balance2_ne_leaf (l : rbnode α) (x r v t) : balance2 l x r v t ≠ leaf :=
by cases l; cases r; simp [balance2]; intro; contradiction

lemma balance2_node_ne_leaf {s : rbnode α} (a : α) (t : rbnode α) : s ≠ leaf → balance2_node s a t ≠ leaf :=
begin
  intro h, cases s,
  { contradiction },
  all_goals { simp [balance2_node], apply balance2_ne_leaf }
end

variables (lt : α → α → Prop) [decidable_rel lt]

open color

@[elab_as_eliminator]
lemma ins.induction {p : rbnode α → Prop}
  (t x)
  (h₁ : p leaf)
  (h₂ : ∀ a y b (hc : cmp_using lt x y = ordering.lt) (ih : p a), p (red_node a y b))
  (h₃ : ∀ a y b (hc : cmp_using lt x y = ordering.eq), p (red_node a y b))
  (h₄ : ∀ a y b (hc : cmp_using lt x y = ordering.gt) (ih : p b), p (red_node a y b))
  (h₅ : ∀ a y b (hc : cmp_using lt x y = ordering.lt) (hr : get_color a = red) (ih : p a), p (black_node a y b))
  (h₆ : ∀ a y b (hc : cmp_using lt x y = ordering.lt) (hnr : get_color a ≠ red) (ih : p a), p (black_node a y b))
  (h₇ : ∀ a y b (hc : cmp_using lt x y = ordering.eq), p (black_node a y b))
  (h₈ : ∀ a y b (hc : cmp_using lt x y = ordering.gt) (hr : get_color b = red) (ih : p b), p (black_node a y b))
  (h₉ : ∀ a y b (hc : cmp_using lt x y = ordering.gt) (hnr : get_color b ≠ red) (ih : p b), p (black_node a y b))
  : p t :=
begin
  induction t,
  case leaf { apply h₁ },
  case red_node a y b {
     cases h : cmp_using lt x y,
     case ordering.lt { apply h₂; assumption },
     case ordering.eq { apply h₃; assumption },
     case ordering.gt { apply h₄; assumption },
   },
  case black_node a y b {
     cases h : cmp_using lt x y,
     case ordering.lt {
       by_cases get_color a = red,
       { apply h₅; assumption },
       { apply h₆; assumption },
     },
     case ordering.eq { apply h₇; assumption },
     case ordering.gt {
       by_cases get_color b = red,
       { apply h₈; assumption },
       { apply h₉; assumption },
     }
  }
end

lemma is_searchable_balance1 {l y r v t lo hi} (hl : is_searchable lt l lo (some y)) (hr : is_searchable lt r (some y) (some v)) (ht : is_searchable lt t (some v) hi) : is_searchable lt (balance1 l y r v t) lo hi :=
by cases l; cases r; simp [balance1]; is_searchable_tactic

lemma is_searchable_balance1_node {t} [is_trans α lt] : ∀ {y s lo hi}, is_searchable lt t lo (some y) → is_searchable lt s (some y) hi → is_searchable lt (balance1_node t y s) lo hi :=
begin
  cases t; simp [balance1_node]; intros; is_searchable_tactic,
  { cases lo,
    { apply is_searchable_none_low_of_is_searchable_some_low, assumption },
    { simp at *, apply is_searchable_some_low_of_is_searchable_of_lt; assumption } },
  all_goals { apply is_searchable_balance1; assumption }
end

lemma is_searchable_balance2 {l y r v t lo hi} (ht : is_searchable lt t lo (some v)) (hl : is_searchable lt l (some v) (some y)) (hr : is_searchable lt r (some y) hi) : is_searchable lt (balance2 l y r v t) lo hi :=
by cases l; cases r; simp [balance2]; is_searchable_tactic

lemma is_searchable_balance2_node {t} [is_trans α lt] : ∀ {y s lo hi}, is_searchable lt s lo (some y) → is_searchable lt t (some y) hi → is_searchable lt (balance2_node t y s) lo hi :=
begin
  induction t; simp [balance2_node]; intros; is_searchable_tactic,
  { cases hi,
    { apply is_searchable_none_high_of_is_searchable_some_high, assumption },
    { simp at *, apply is_searchable_some_high_of_is_searchable_of_lt, assumption' } },
  all_goals { apply is_searchable_balance2, assumption' }
end

lemma is_searchable_ins {t x} [is_strict_weak_order α lt] : ∀ {lo hi} (h : is_searchable lt t lo hi), lift lt lo (some x) → lift lt (some x) hi → is_searchable lt (ins lt t x) lo hi :=
begin
  apply ins.induction lt t x; intros; simp [ins, *] at * {eta := ff}; is_searchable_tactic,
  { apply ih h_hs₁, assumption, simp [*] },
  { apply is_searchable_of_is_searchable_of_incomp hc, assumption },
  { apply is_searchable_of_incomp_of_is_searchable hc, assumption },
  { apply ih h_hs₂, cases hi; simp [*], assumption },
  { apply is_searchable_balance1_node, apply ih h_hs₁, assumption, simp [*], assumption },
  { apply ih h_hs₁, assumption, simp [*] },
  { apply is_searchable_of_is_searchable_of_incomp hc, assumption },
  { apply is_searchable_of_incomp_of_is_searchable hc, assumption },
  { apply is_searchable_balance2_node, assumption, apply ih h_hs₂, simp [*], assumption },
  { apply ih h_hs₂, assumption, simp [*] }
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

local infix `∈` := mem lt
local attribute [simp] mem balance1 balance2 balance1_node balance2_node

lemma mem_balance1_node_of_mem_left {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance1_node s v t :=
begin
  cases s,
  { simp [mem] },
  all_goals {
    intro h,
    simp, cases s_lchild; cases s_rchild,
    any_goals { simp [*] at * },
    all_goals { blast_disjs; simp [*] }
  }
end

lemma mem_balance2_node_of_mem_left {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance2_node s v t :=
begin
  cases s,
  { simp [mem] },
  all_goals {
    intro h,
    simp, cases s_lchild; cases s_rchild,
    any_goals { simp [*] at * },
    all_goals { blast_disjs; simp [*] }
  }
end

lemma mem_balance1_node_of_mem_right {x t} (v) (s : rbnode α) : x ∈ t → x ∈ balance1_node s v t :=
begin
  intros, cases s,
  { simp [*] },
  all_goals { simp, cases s_lchild; cases s_rchild; simp [*] }
end

lemma mem_balance2_node_of_mem_right {x t} (v) (s : rbnode α) : x ∈ t → x ∈ balance2_node s v t :=
begin
  intros, cases s,
  { simp [*] },
  all_goals { simp, cases s_lchild; cases s_rchild; simp [*] }
end

lemma mem_balance1_node_of_incomp {x v} (s t) : (¬ lt x v ∧ ¬ lt v x) → s ≠ leaf → x ∈ balance1_node s v t :=
begin
  intros, cases s,
  case leaf { contradiction },
  all_goals { simp, cases s_lchild; cases s_rchild; simp [*] }
end

lemma mem_balance2_node_of_incomp {x v} (s t) : (¬ lt v x ∧ ¬ lt x v) → s ≠ leaf → x ∈ balance2_node s v t :=
begin
  intros, cases s,
  case leaf { contradiction },
  all_goals { simp, cases s_lchild; cases s_rchild; simp [*] }
end

lemma ins_ne_leaf (t : rbnode α) (x : α) : t.ins lt x ≠ leaf :=
begin
  apply ins.induction lt t x,
  any_goals { intros, simp [ins, *], contradiction},
  { intros, simp [ins, *], apply balance1_node_ne_leaf, assumption },
  { intros, simp [ins, *], apply balance2_node_ne_leaf, assumption },
end

lemma insert_ne_leaf (t : rbnode α) (x : α) : insert lt t x ≠ leaf :=
begin
  simp [insert],
  cases he : ins lt t x; cases get_color t; simp [mk_insert_result],
  { have := ins_ne_leaf lt t x, contradiction },
  any_goals { contradiction },
  { exact absurd he (ins_ne_leaf _ _ _) }
end

lemma mem_ins_of_incomp (t : rbnode α) {x y : α} : ∀ h : ¬ lt x y ∧ ¬ lt y x, x ∈ t.ins lt y :=
begin
  apply ins.induction lt t y,
  { simp [ins], apply id },
  any_goals { intros, simp [ins, *] },
  { have := ih h, apply mem_balance1_node_of_mem_left, assumption },
  { have := ih h, apply mem_balance2_node_of_mem_left, assumption }
end

lemma mem_ins_of_mem [is_strict_weak_order α lt] {t : rbnode α} (z : α) : ∀ {x} (h : x ∈ t), x ∈ t.ins lt z :=
begin
  apply ins.induction lt t z; intros,
  { simp [mem, ins] at h, contradiction },
  all_goals { simp [ins, *] at *, blast_disjs },
  any_goals { simp [h] },
  any_goals { simp [ih h] },
  { have := incomp_trans_of lt h ⟨hc.2, hc.1⟩, simp [this] },
  { apply mem_balance1_node_of_mem_left, apply ih h },
  { have := ins_ne_leaf lt a z, apply mem_balance1_node_of_incomp, cases h, all_goals { simp [*] } },
  { apply mem_balance1_node_of_mem_right, assumption },
  { have := incomp_trans_of lt hc ⟨h.2, h.1⟩, simp [this] },
  { apply mem_balance2_node_of_mem_right, assumption },
  { have := ins_ne_leaf lt a z, apply mem_balance2_node_of_incomp, cases h, simp [*], apply ins_ne_leaf },
  { apply mem_balance2_node_of_mem_left, apply ih h }
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
  cases s,
  { simp, intros, simp [*] },
  all_goals { cases s_lchild; cases s_rchild; simp; intros; blast_disjs; simp [*] },
end

lemma of_mem_balance2_node [is_strict_weak_order α lt] {x s v t} : x ∈ balance2_node s v t → x ∈ s ∨ (¬ lt x v ∧ ¬ lt v x) ∨ x ∈ t :=
begin
  cases s,
  { simp, intros, simp [*] },
  all_goals { cases s_lchild; cases s_rchild; simp; intros; blast_disjs; simp [*] }
end

lemma equiv_or_mem_of_mem_ins [is_strict_weak_order α lt] {t : rbnode α} {x z} : ∀ (h : x ∈ t.ins lt z), x ≈[lt] z ∨ x ∈ t :=
begin
  apply ins.induction lt t z; intros; simp [ins, strict_weak_order.equiv, *] at *; blast_disjs,
  any_goals { simp [h] },
  any_goals { have ih := ih h, cases ih; simp [*], done },
  { have h' := of_mem_balance1_node lt h, blast_disjs, have := ih h', blast_disjs, all_goals { simp [*] } },
  { have h' := of_mem_balance2_node lt h, blast_disjs, have := ih h', blast_disjs, all_goals { simp [*] } }
end

lemma equiv_or_mem_of_mem_insert [is_strict_weak_order α lt] {t : rbnode α} {x z} : ∀ (h : x ∈ t.insert lt z), x ≈[lt] z ∨ x ∈ t :=
begin
  simp [insert], intros, apply equiv_or_mem_of_mem_ins, exact mem_of_mem_mk_insert_result lt h
end

lemma mem_exact_balance1_node_of_mem_exact {x s} (v) (t : rbnode α) : mem_exact x s → mem_exact x (balance1_node s v t) :=
begin
  cases s,
  { simp [mem_exact] },
  all_goals {
    intro h,
    simp [balance1_node], cases s_lchild; cases s_rchild,
    any_goals { simp [*, mem_exact] at * },
    all_goals { blast_disjs; simp [*] }
  }
end

lemma mem_exact_balance2_node_of_mem_exact {x s} (v) (t : rbnode α) : mem_exact x s → mem_exact x (balance2_node s v t) :=
begin
  cases s,
  { simp [mem_exact] },
  all_goals {
    intro h,
    simp [balance2_node], cases s_lchild; cases s_rchild,
    any_goals { simp [*, mem_exact] at * },
    all_goals { blast_disjs; simp [*] }
  }
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

lemma weak_trichotomous (x y) : lt x y ∨ (¬ lt x y ∧ ¬ lt y x) ∨ lt y x :=
by by_cases lt x y; by_cases lt y x; simp [*]

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
  cases l; cases r; simp [balance1, *]; is_searchable_tactic,
  { have h₁ := weak_trichotomous lt x v, blast_disjs,
    { have := trans h₁ (lo_lt_hi hr_hs₁), simp [*] },
    { have := lt_of_incomp_of_lt h₁ (lo_lt_hi hr_hs₁),
      simp [*] },
    { have h := weak_trichotomous lt x r_val, blast_disjs; simp [*] } },
  { have := weak_trichotomous lt x v, blast_disjs; simp [*] },
  { have := weak_trichotomous lt x v, blast_disjs; simp [*] },
  { have := weak_trichotomous lt x v, blast_disjs; simp [*] },
  { have hvv_1 := lo_lt_hi hr_hs₁,
    have h₁ := weak_trichotomous lt x v, blast_disjs,
    { have := trans h₁ hvv_1, simp [*] },
    { have := lt_of_incomp_of_lt h₁ (lo_lt_hi hr_hs₁),
      simp [*] },
    { have h₂ := weak_trichotomous lt x r_val, blast_disjs; simp [*] } }
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
  cases l; cases r; simp [balance1, *]; is_searchable_tactic,
  { have := trans_of lt (lo_lt_hi hr_hs₂) h, simp [*] },
  { have := trans_of lt hr_hlt h, simp [*] },
  iterate 2 { have := trans_of lt (trans (lo_lt_hi hr_hs₁) (lo_lt_hi hr_hs₂)) h, simp [*] },
  { have := trans_of lt (lo_lt_hi hr_hs₂) h, simp [*] }
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
  cases l; cases r; simp [balance1, *]; is_searchable_tactic,
  { have : lt r_val x := lt_of_lt_of_incomp (lo_lt_hi hr_hs₂) h.swap, simp [*] },
  { have : lt v x := lt_of_lt_of_incomp hr_hlt h.swap, simp [*] },
  iterate 2 {
    have : lt v x := lt_of_lt_of_incomp (trans (lo_lt_hi hr_hs₁) (lo_lt_hi hr_hs₂)) h.swap,
    simp [*] },
  { have : lt r_val x := lt_of_lt_of_incomp (lo_lt_hi hr_hs₂) h.swap, simp [*] }
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
  cases l; cases r; simp [balance2, *]; is_searchable_tactic,
  { have := trans h hl_hlt, simp [*] },
  { have := trans h (lo_lt_hi hl_hs₁), simp [*] },
  iterate 2 { have := trans h (lo_lt_hi hl_hs₁), simp [*] },
  { have := trans h (trans (lo_lt_hi hl_hs₁) (lo_lt_hi hl_hs₂)), simp [*] }
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
  cases l; cases r; simp [balance2, *]; is_searchable_tactic,
  { have := weak_trichotomous lt x v, blast_disjs; simp [*] },
  all_goals {
    have h₁ := weak_trichotomous lt x l_val, blast_disjs,
    { have := trans h₁ (lo_lt_hi hl_hs₂), simp [*] },
    { have := lt_of_incomp_of_lt h₁ (lo_lt_hi hl_hs₂), simp [*] },
    { have := weak_trichotomous lt x v, blast_disjs; simp [*] } }
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
  cases l; cases r; simp [balance2, *]; is_searchable_tactic,
  { have : lt x v := lt_of_incomp_of_lt h hl_hlt, simp [*] },
  any_goals { have : lt x l_val := lt_of_incomp_of_lt h (lo_lt_hi hl_hs₁), simp [*] },
  { have : lt x v := lt_of_incomp_of_lt h (trans (lo_lt_hi hl_hs₁) (lo_lt_hi hl_hs₂)), simp [*] }
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
