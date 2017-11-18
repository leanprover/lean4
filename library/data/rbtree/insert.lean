/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.rbtree.basic
universe u

/- TODO(Leo): remove after we cleanup stdlib simp lemmas -/
local attribute [-simp] or.comm or.left_comm or.assoc and.comm and.left_comm and.assoc

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
  (h₉ : ∀ a y b (hc : cmp_using lt x y = ordering.gt) (hr : get_color b ≠ red) (ih : p b), p (black_node a y b))
  : p t :=
begin
  induction t,
  case leaf { apply h₁ },
  case red_node a y b {
     generalize h : cmp_using lt x y = c,
     cases c,
     case ordering.lt { apply h₂, assumption, assumption },
     case ordering.eq { apply h₃, assumption },
     case ordering.gt { apply h₄, assumption, assumption },
   },
  case black_node a y b {
     generalize h : cmp_using lt x y = c,
     cases c,
     case ordering.lt {
       by_cases get_color a = red,
       { apply h₅, assumption, assumption, assumption },
       { apply h₆, assumption, assumption, assumption },
     },
     case ordering.eq { apply h₇, assumption },
     case ordering.gt {
       by_cases get_color b = red,
       { apply h₈, assumption, assumption, assumption },
       { apply h₉, assumption, assumption, assumption },
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
    { simp [lift] at *, apply is_searchable_some_low_of_is_searchable_of_lt, assumption, assumption } },
  all_goals { apply is_searchable_balance1, repeat { assumption } }
end

lemma is_searchable_balance2 {l y r v t lo hi} (ht : is_searchable lt t lo (some v)) (hl : is_searchable lt l (some v) (some y)) (hr : is_searchable lt r (some y) hi) : is_searchable lt (balance2 l y r v t) lo hi :=
by cases l; cases r; simp [balance2]; is_searchable_tactic

lemma is_searchable_balance2_node {t} [is_trans α lt] : ∀ {y s lo hi}, is_searchable lt s lo (some y) → is_searchable lt t (some y) hi → is_searchable lt (balance2_node t y s) lo hi :=
begin
  induction t; simp [balance2_node]; intros; is_searchable_tactic,
  { cases hi,
    { apply is_searchable_none_high_of_is_searchable_some_high, assumption },
    { simp [lift] at *, apply is_searchable_some_high_of_is_searchable_of_lt, assumption, assumption } },
  all_goals { apply is_searchable_balance2, repeat { assumption } }
end

lemma is_searchable_ins {t x} [is_strict_weak_order α lt] : ∀ {lo hi} (h : is_searchable lt t lo hi), lift lt lo (some x) → lift lt (some x) hi → is_searchable lt (ins lt t x) lo hi :=
begin
  apply ins.induction lt t x; intros; simp [ins, lift, *] at * {eta := ff}; is_searchable_tactic,
  { apply ih hs₁, assumption, simp [lift, *] },
  { apply is_searchable_of_is_searchable_of_incomp hc, assumption },
  { apply is_searchable_of_incomp_of_is_searchable hc, assumption },
  { apply ih hs₂, cases hi; simp [lift, *], assumption },
  { apply is_searchable_balance1_node, apply ih hs₁, assumption, simp [lift, *], assumption },
  { apply ih hs₁, assumption, simp [lift, *] },
  { apply is_searchable_of_is_searchable_of_incomp hc, assumption },
  { apply is_searchable_of_incomp_of_is_searchable hc, assumption },
  { apply is_searchable_balance2_node, assumption, apply ih hs₂, simp [lift, *], assumption },
  { apply ih hs₂, assumption, simp [lift, *] }
end

lemma is_searchable_flip_red {t} : is_searchable lt t none none → is_searchable lt (flip_red t) none none :=
begin
  cases t; simp [flip_red],
  any_goals { exact id },
  { intro h, is_searchable_tactic }
end

lemma is_searchable_insert {t x} [is_strict_weak_order α lt] : is_searchable lt t none none → is_searchable lt (insert lt t x) none none :=
begin
  intro h, simp [insert], apply is_searchable_flip_red, apply is_searchable_ins, assumption, simp [lift], simp [lift]
end

end rbnode


namespace rbnode
section membership_lemmas
parameters {α : Type u} (lt : α → α → Prop) [decidable_rel lt]

local infix `∈` := mem lt

lemma mem_balance1_node_of_mem_left {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance1_node s v t :=
begin
  cases s,
  { simp [mem] },
  all_goals {
    intro h,
    simp [balance1_node], cases lchild; cases rchild,
    any_goals { simp [*, mem, balance1] at * },
    all_goals { blast_disjs; simp [*] }
  }
end

lemma mem_balance2_node_of_mem_left {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance2_node s v t :=
begin
  cases s,
  { simp [mem] },
  all_goals {
    intro h,
    simp [balance2_node], cases lchild; cases rchild,
    any_goals { simp [*, mem, balance2] at * },
    all_goals { blast_disjs; simp [*] }
  }
end

lemma mem_balance1_node_of_mem_right {x t} (v) (s : rbnode α) : x ∈ t → x ∈ balance1_node s v t :=
begin
  intros, cases s,
  { simp [mem, balance1_node, *] },
  all_goals { simp [balance1_node], cases lchild; cases rchild; simp [*, mem, balance1] }
end

lemma mem_balance2_node_of_mem_right {x t} (v) (s : rbnode α) : x ∈ t → x ∈ balance2_node s v t :=
begin
  intros, cases s,
  { simp [mem, balance2_node, *] },
  all_goals { simp [balance2_node], cases lchild; cases rchild; simp [*, mem, balance2] }
end

lemma mem_balance1_node_of_incomp {x v} (s t) : (¬ lt x v ∧ ¬ lt v x) → s ≠ leaf → x ∈ balance1_node s v t :=
begin
  intros, cases s,
  case leaf { contradiction },
  all_goals { simp [balance1_node], cases lchild; cases rchild; simp [*, mem, balance1] }
end

lemma mem_balance2_node_of_incomp {x v} (s t) : (¬ lt v x ∧ ¬ lt x v) → s ≠ leaf → x ∈ balance2_node s v t :=
begin
  intros, cases s,
  case leaf { contradiction },
  all_goals { simp [balance2_node], cases lchild; cases rchild; simp [*, mem, balance2] }
end

lemma ins_ne_leaf (t : rbnode α) (x : α) : t.ins lt x ≠ leaf :=
begin
  apply ins.induction lt t x,
  any_goals { intros, simp [ins, *], contradiction},
  { intros, simp [ins, *], apply balance1_node_ne_leaf, assumption },
  { intros, simp [ins, *], apply balance2_node_ne_leaf, assumption },
end

lemma mem_ins_of_incomp (t : rbnode α) {x y : α} : ∀ h : ¬ lt x y ∧ ¬ lt y x, x ∈ t.ins lt y :=
begin
  apply ins.induction lt t y,
  { simp [ins, mem], apply id },
  any_goals { intros, simp [ins, mem, *] },
  { have := ih h, apply mem_balance1_node_of_mem_left, assumption },
  { have := ih h, apply mem_balance2_node_of_mem_left, assumption }
end

lemma mem_ins_of_mem [is_strict_weak_order α lt] {t : rbnode α} (z : α) : ∀ {x} (h : x ∈ t), x ∈ t.ins lt z :=
begin
  apply ins.induction lt t z; intros,
  { simp [mem, ins] at h, contradiction },
  all_goals { simp [ins, mem, *] at *, blast_disjs },
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

lemma mem_flip_red {a t} : mem lt a t → mem lt a (flip_red t) :=
by intros; cases t; simp [flip_red, mem, *] at *

lemma mem_of_mem_flip_red {a t} : mem lt a (flip_red t) → mem lt a t :=
by cases t; simp [flip_red, mem]; intros; assumption

lemma mem_insert_of_incomp (t : rbnode α) {x y : α} : ∀ h : ¬ lt x y ∧ ¬ lt y x, x ∈ t.insert lt y :=
by intros; unfold insert; apply mem_flip_red; apply mem_ins_of_incomp; assumption

lemma mem_insert_of_mem [is_strict_weak_order α lt] {t x} (z) : x ∈ t → x ∈ t.insert lt z :=
by intros; apply mem_flip_red; apply mem_ins_of_mem; assumption

lemma of_mem_balance1_node [is_strict_weak_order α lt] {x s v t} : x ∈ balance1_node s v t → x ∈ s ∨ (¬ lt x v ∧ ¬ lt v x) ∨ x ∈ t :=
begin
  cases s,
  { simp [mem, balance1_node], intros, simp [*] },
  all_goals { cases lchild; cases rchild; simp [mem, balance1, balance1_node]; intros; blast_disjs; simp [*] }
end

lemma of_mem_balance2_node [is_strict_weak_order α lt] {x s v t} : x ∈ balance2_node s v t → x ∈ s ∨ (¬ lt x v ∧ ¬ lt v x) ∨ x ∈ t :=
begin
  cases s,
  { simp [mem, balance2_node], intros, simp [*] },
  all_goals { cases lchild; cases rchild; simp [mem, balance2, balance2_node]; intros; blast_disjs; simp [*] }
end

lemma equiv_or_mem_of_mem_ins [is_strict_weak_order α lt] {t : rbnode α} {x z} : ∀ (h : x ∈ t.ins lt z), x ≈[lt] z ∨ x ∈ t :=
begin
  apply ins.induction lt t z; intros; simp [mem, ins, strict_weak_order.equiv, *] at *; blast_disjs,
  any_goals { simp [h] },
  any_goals { have ih := ih h, cases ih; simp [*], done },
  { have h := of_mem_balance1_node lt h, blast_disjs, have := ih h, blast_disjs, all_goals { simp [*] } },
  { have h := of_mem_balance2_node lt h, blast_disjs, have := ih h, blast_disjs, all_goals { simp [*] } }
end

lemma equiv_or_mem_of_mem_insert [is_strict_weak_order α lt] {t : rbnode α} {x z} : ∀ (h : x ∈ t.insert lt z), x ≈[lt] z ∨ x ∈ t :=
begin
  simp [insert], intros, apply equiv_or_mem_of_mem_ins, exact mem_of_mem_flip_red lt h
end

end membership_lemmas

end rbnode
