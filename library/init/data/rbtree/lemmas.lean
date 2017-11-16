/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import init.data.rbtree.basic init.meta init.data.nat

universes u v

/- TODO(Leo): remove after we cleanup stdlib simp lemmas -/
local attribute [-simp] or.comm or.left_comm or.assoc

namespace tactic
/- TODO(Leo): move blast_disjs to another file. -/
private meta def blast_disjs_aux : list expr → tactic unit
| []      := failed
| (h::hs) := do
  t ← infer_type h,
  if t.is_or = none then blast_disjs_aux hs
  else do
    cases h [h.local_pp_name, h.local_pp_name],
    return ()

namespace interactive

meta def blast_disjs : tactic unit :=
focus1 $ repeat $ any_goals $ local_context >>= blast_disjs_aux

end interactive
end tactic

namespace rbnode
variables {α : Type u} {β : Type v}

open color nat

def lift (lt : α → α → Prop) : option α → option α → Prop
| (some a) (some b) := lt a b
| none     (some b) := true
| _         _       := false

instance lift_lt_trans (lt : α → α → Prop) [is_trans α lt] : is_trans (option α) (lift lt) :=
begin
  constructor,
  intros a b c,
  cases a with a; cases b with b; cases c with c; simp [lift],
  apply trans_of lt
end

instance lift_lt_irrefl (lt : α → α → Prop) [is_irrefl α lt] : is_irrefl (option α) (lift lt) :=
begin
  constructor,
  intros a, cases a; simp [lift],
  apply irrefl_of lt
end

instance lift_lt_incomp_trans (lt : α → α → Prop) [is_incomp_trans α lt] : is_incomp_trans (option α) (lift lt) :=
begin
  constructor,
  intros a b c, cases a; cases b; cases c; simp [lift],
  apply incomp_trans_of lt
end

instance (lt : α → α → Prop) [is_strict_weak_order α lt] : is_strict_weak_order (option α) (lift lt) :=
{ trans        := λ a b c, trans_of (lift lt),
  irrefl       := irrefl_of (lift lt),
  incomp_trans := λ a b c, incomp_trans_of (lift lt) }

instance (lt : α → α → Prop) [h : decidable_rel lt] : decidable_rel (lift lt)
| none     none     := is_false not_false
| none     (some b) := is_true trivial
| (some a) none     := is_false not_false
| (some a) (some b) := h a b

lemma lift_lt_of_lt (lt : α → α → Prop) : ∀ {a b}, lt a b → lift lt (some a) (some b) :=
begin simp [lift], intros, assumption end

lemma not_lift_lt_of_not_lt (lt : α → α → Prop) : ∀ {a b}, ¬ lt a b → ¬ lift lt (some a) (some b) :=
begin simp [lift], intros, assumption end

inductive is_searchable (lt : α → α → Prop) : rbnode α → option α → option α → Prop
| leaf_s  {lo hi}       : lift lt lo hi → is_searchable leaf lo hi
| red_s   {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) : is_searchable (red_node l v r) lo hi
| black_s {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) : is_searchable (black_node l v r) lo hi

open rbnode (mem)
open is_searchable

lemma lo_lt_hi {t : rbnode α} {lt} [is_trans α lt] : ∀ {lo hi}, is_searchable lt t lo hi → lift lt lo hi :=
begin
  induction t; intros lo hi h,
  case leaf { cases h, assumption },
  all_goals {
    cases h,
    have h₁ := ih_1 ‹is_searchable lt lchild lo (some val)›,
    have h₂ := ih_2 ‹is_searchable lt rchild (some val) hi›,
    apply trans_of (lift lt) h₁ h₂
  }
end

lemma range {t : rbnode α} {lt x} [decidable_rel lt] [is_strict_weak_order α lt] : ∀ {lo hi}, is_searchable lt t lo hi → mem lt x t → lift lt lo (some x) ∧ lift lt (some x) hi :=
begin
  induction t,
  case leaf f{ simp [mem], intros, trivial },
  all_goals { -- red_node and black_node are identical
    intros lo hi h₁ h₂, cases h₁,
    simp only [mem] at h₂,
    have val_hi : lift lt (some val) hi, { apply lo_lt_hi, assumption },
    have lo_val : lift lt lo (some val), { apply lo_lt_hi, assumption },
    blast_disjs,
    {
      have h₃ : lift lt lo (some x) ∧ lift lt (some x) (some val), { apply ih_1, assumption, assumption },
      cases h₃ with lo_x x_val,
      split,
      show lift lt lo (some x), { assumption },
      show lift lt (some x ) hi, { apply trans_of (lift lt) x_val val_hi },
    },
    {
      simp at h₂, cases h₂,
      split,
      { apply lt_of_lt_of_incomp lo_val, split, repeat { assumption } },
      { apply lt_of_incomp_of_lt _ val_hi, split, repeat { assumption }  }
    },
    {
      have h₃ : lift lt (some val) (some x) ∧ lift lt (some x) hi, { apply ih_2, assumption, assumption },
      cases h₃ with val_x x_hi,
      split,
      show lift lt lo (some x), { apply trans_of (lift lt) lo_val val_x },
      show lift lt (some x) hi, { assumption }
    }
  }
end

@[elab_simple]
lemma contains.induction {p : rbnode α → Prop} (lt) [decidable_rel lt]
   (t x)
   (h₁ : p leaf)
   (h₂ : ∀ l y r (h : cmp_using lt x y = ordering.lt) (ih : p l), p (red_node l y r))
   (h₃ : ∀ l y r (h : cmp_using lt x y = ordering.eq),            p (red_node l y r))
   (h₄ : ∀ l y r (h : cmp_using lt x y = ordering.gt) (ih : p r), p (red_node l y r))
   (h₅ : ∀ l y r (h : cmp_using lt x y = ordering.lt) (ih : p l), p (black_node l y r))
   (h₆ : ∀ l y r (h : cmp_using lt x y = ordering.eq),            p (black_node l y r))
   (h₇ : ∀ l y r (h : cmp_using lt x y = ordering.gt) (ih : p r), p (black_node l y r))
   : p t :=
begin
  induction t,
  case leaf {assumption},
  case red_node l y r {
     generalize h : cmp_using lt x y = c,
     cases c,
     case ordering.lt { apply h₂, assumption, assumption },
     case ordering.eq { apply h₃, assumption },
     case ordering.gt { apply h₄, assumption, assumption },
  },
  case black_node l y r {
     generalize h : cmp_using lt x y = c,
     cases c,
     case ordering.lt { apply h₅, assumption, assumption },
     case ordering.eq { apply h₆, assumption },
     case ordering.gt { apply h₇, assumption, assumption },
  }
end

lemma contains_correct {t : rbnode α} {lt x} [decidable_rel lt] [is_strict_weak_order α lt] : ∀ {lo hi} (hs : is_searchable lt t lo hi), mem lt x t ↔ contains lt t x = tt :=
begin
  apply contains.induction lt t x; intros; simp only [mem, contains, *],
  { simp },
  any_goals {
    /- Solve minor premises h₂ and h₅ -/
    cases hs,
    apply iff.intro,
    {
      intro hm, blast_disjs,
      { exact iff.mp (ih hs₁) hm },
      { contradiction },
      {
        have hyx : lift lt (some y) (some x) := (range hs₂ hm).1,
        simp [lift] at hyx,
        have hxy : lt x y, { simp [cmp_using] at h, assumption },
        exact absurd (trans_of lt hxy hyx) (irrefl_of lt x)
      }
    },
    { intro hc, left, exact iff.mpr (ih hs₁) hc },
    done
 },
 any_goals {
    /- Solve minor premises h₃ and h₆ -/
    simp, done
 },
 any_goals {
   /- Solve minor premises h₄ and h₇ -/
   cases hs,
   apply iff.intro,
   {
     intro hm, blast_disjs,
     {
       have hxy : lift lt (some x) (some y) := (range hs₁ hm).2,
       simp [lift] at hxy,
       have hyx : lt y x, { simp [cmp_using] at h, exact h.1 },
       exact absurd (trans_of lt hxy hyx) (irrefl_of lt x)
     },
     { contradiction },
     { exact iff.mp (ih hs₂) hm }
   },
   { intro hc, right, right, exact iff.mpr (ih hs₂) hc },
   done
 }
end

inductive is_red_black : rbnode α → color → nat → Prop
| leaf_rb  : is_red_black leaf black 0
| red_rb   : ∀ {v l r n}, is_red_black l black n → is_red_black r black n → is_red_black (red_node l v r) red n
| black_rb : ∀ {v l r n c₁ c₂}, is_red_black l c₁ n → is_red_black r c₂ n → is_red_black (black_node l v r) black (succ n)

open is_red_black

def depth (f : nat → nat → nat) : rbnode α → nat
| leaf               := 0
| (red_node l _ r)   := succ (f (depth l) (depth r))
| (black_node l _ r) := succ (f (depth l) (depth r))

lemma depth_min : ∀ {c n} {t : rbnode α}, is_red_black t c n → depth min t ≥ n :=
begin
  intros c n' t h,
  induction h,
  case leaf_rb {apply le_refl},
  case red_rb { simp [depth],
    have : min (depth min l) (depth min r) ≥ n,
    { apply le_min, repeat {assumption}},
    apply le_succ_of_le, assumption },
  case black_rb { simp [depth],
    apply succ_le_succ,
    apply le_min, repeat {assumption} }
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
    suffices : succ (max (depth max l) (depth max r)) ≤ 2 * n + 1,
    { simp [depth, upper, *] at * },
    apply succ_le_succ,
    apply max_le, repeat {assumption}},
  case black_rb {
    have : depth max l ≤ 2*n + 1, from le_trans ih_1 (upper_le _ _),
    have : depth max r ≤ 2*n + 1, from le_trans ih_2 (upper_le _ _),
    suffices new : max (depth max l) (depth max r) + 1 ≤ 2 * n + 2*1,
    { simp [depth, upper, succ_eq_add_one, left_distrib, *] at * },
    apply succ_le_succ, apply max_le, repeat {assumption}
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

lemma balance1_rb {l r t : rbnode α} {y v : α} {c_l c_r c_t n} : is_red_black l c_l n → is_red_black r c_r n → is_red_black t c_t n → ∃ c, is_red_black (balance1 l y r v t) c (succ n) :=
begin
  intros h₁ h₂ h₃, cases h₁; cases h₂; repeat {assumption <|> constructor},
end

lemma balance2_rb {l r t : rbnode α} {y v : α} {c_l c_r c_t n} : is_red_black l c_l n → is_red_black r c_r n → is_red_black t c_t n → ∃ c, is_red_black (balance2 l y r v t) c (succ n) :=
begin
  intros h₁ h₂ h₃, cases h₁; cases h₂; repeat {assumption <|> constructor},
end

lemma balance1_ne_leaf (l : rbnode α) (x r v t) : balance1 l x r v t ≠ leaf :=
by cases l; cases r; simp [balance1]; intro; contradiction

lemma balance1_node_ne_leaf {s : rbnode α} (a : α) (t : rbnode α) : s ≠ leaf → balance1_node s a t ≠ leaf :=
begin
  intro h,
  induction s,
  case leaf       { contradiction},
  case red_node   { simp [balance1_node], apply balance1_ne_leaf },
  case black_node { simp [balance1_node], apply balance1_ne_leaf }
end

lemma balance2_ne_leaf (l : rbnode α) (x r v t) : balance2 l x r v t ≠ leaf :=
by cases l; cases r; simp [balance2]; intro; contradiction

lemma balance2_node_ne_leaf {s : rbnode α} (a : α) (t : rbnode α) : s ≠ leaf → balance2_node s a t ≠ leaf :=
begin
  intro h,
  induction s,
  case leaf       { contradiction},
  case red_node   { simp [balance2_node], apply balance2_ne_leaf },
  case black_node { simp [balance2_node], apply balance2_ne_leaf }
end

section insert
variables (lt : α → α → Prop) [decidable_rel lt]

@[elab_as_eliminator]
lemma ins.induction {p : rbnode α → Prop}
  (t x)
  (h₁ : p leaf)
  (h₂ : ∀ a y b, cmp_using lt x y = ordering.lt → p a → p (red_node a y b))
  (h₃ : ∀ a y b, cmp_using lt x y = ordering.eq → p (red_node a y b))
  (h₄ : ∀ a y b, cmp_using lt x y = ordering.gt → p b → p (red_node a y b))
  (h₅ : ∀ a y b, cmp_using lt x y = ordering.lt → get_color a = red → p a → p (black_node a y b))
  (h₆ : ∀ a y b, cmp_using lt x y = ordering.lt → get_color a ≠ red → p a → p (black_node a y b))
  (h₇ : ∀ a y b, cmp_using lt x y = ordering.eq → p (black_node a y b))
  (h₈ : ∀ a y b, cmp_using lt x y = ordering.gt → get_color b = red → p b → p (black_node a y b))
  (h₉ : ∀ a y b, cmp_using lt x y = ordering.gt → get_color b ≠ red → p b → p (black_node a y b))
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

end insert

end rbnode

namespace rbnode

section membership_lemmas
parameters {α : Type u} (lt : α → α → Prop) [decidable_rel lt]

local infix `∈` := rbnode.mem lt

lemma mem_balance1_node {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance1_node s v t :=
begin
  cases s,
  case leaf { simp [rbnode.mem] },
  case red_node l v r {
    intro h,
    simp [balance1_node], cases l; cases r,
    any_goals { simp [*, rbnode.mem, balance1] at * },
    all_goals { blast_disjs; simp [*] }
  },
  case black_node l v r {
    intro h,
    simp [balance1_node], cases l; cases r,
    any_goals { simp [*, rbnode.mem, balance1] at * },
    all_goals { blast_disjs; simp [*] }
  }
end

lemma mem_balance2_node {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance2_node s v t :=
begin
  cases s,
  case leaf { simp [rbnode.mem] },
  case red_node l v r {
    intro h,
    simp [balance2_node], cases l; cases r,
    any_goals { simp [*, rbnode.mem, balance2] at * },
    all_goals { blast_disjs; simp [*] }
  },
  case black_node l v r {
    intro h,
    simp [balance2_node], cases l; cases r,
    any_goals { simp [*, rbnode.mem, balance2] at * },
    all_goals { blast_disjs; simp [*] }
  }
end

lemma ins_ne_leaf (t : rbnode α) (x : α) : t.ins lt x ≠ leaf :=
begin
  apply ins.induction lt t x,
  any_goals { intros, simp [ins, *], contradiction},
  { intros, simp [ins, *], apply balance1_node_ne_leaf, assumption },
  { intros, simp [ins, *], apply balance2_node_ne_leaf, assumption },
end

lemma mem_ins [is_irrefl α lt] (t : rbnode α) (x : α) : x ∈ t.ins lt x :=
begin
  apply ins.induction lt t x,
  { simp [ins, rbnode.mem], apply irrefl },
  any_goals { intros, simp [ins, rbnode.mem, *] },
  any_goals { right, left, apply irrefl },
  { apply mem_balance1_node, assumption },
  { apply mem_balance2_node, assumption }
end

lemma mem_black_node_of_mem_red_node {l r : rbnode α} {v a : α} : a ∈ red_node l v r → a ∈ black_node l v r :=
λ h, h

lemma mem_insert [is_irrefl α lt] : ∀ (a : α) (t : rbnode α), a ∈ t.insert lt a :=
begin
  intros a t,
  simp [insert],
  have h : ins lt t a ≠ leaf, { apply ins_ne_leaf },
  generalize he : ins lt t a = r,
  cases r; simp [insert],
  case leaf { contradiction },
  case black_node { rw [←he], apply mem_ins },
  case red_node {
    have : a ∈ red_node lchild val rchild, { rw [←he], apply mem_ins },
    apply mem_black_node_of_mem_red_node, assumption
  }
end

end membership_lemmas

end rbnode

namespace rbtree
variables {α : Type u} {lt : α → α → Prop} [decidable_rel lt]

lemma mem_insert [is_irrefl α lt] : ∀ (a : α) (t : rbtree α lt), a ∈ t.insert a
| a ⟨t, _⟩ := t.mem_insert lt a

end rbtree
