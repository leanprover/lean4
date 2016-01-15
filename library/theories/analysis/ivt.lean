/-
Copyright (c) 2015 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

The intermediate value theorem.
-/
import .real_limit
open real analysis set classical
noncomputable theory

private definition inter_sup (a b : ℝ) (f : ℝ → ℝ) := sup {x | x < b ∧ f x < 0}

section
parameters {f : ℝ → ℝ} (Hf : continuous f) {a b : ℝ} (Hab : a < b) (Ha : f a < 0) (Hb : f b > 0)
include Hf Ha Hb Hab

private theorem Hinh : ∃ x, x ∈ {x | x < b ∧ f x < 0} := exists.intro a (and.intro Hab Ha)

private theorem Hmem : ∀ x, x ∈ {x | x < b ∧ f x < 0} → x ≤ b := λ x Hx, le_of_lt (and.left Hx)

private theorem Hsupleb : inter_sup a b f ≤ b := sup_le (Hinh) Hmem

local notation 2 := of_num 1 + of_num 1

private theorem ex_delta_lt {x : ℝ} (Hx : f x < 0) (Hxb : x < b) : ∃ δ : ℝ, δ > 0 ∧ x + δ < b ∧ f (x + δ) < 0 :=
  begin
    let Hcont := neg_on_nbhd_of_cts_of_neg Hf Hx,
    cases Hcont with δ Hδ,
    {cases em (x + δ < b) with Haδ Haδ,
    existsi δ / 2,
    split,
    {exact div_pos_of_pos_of_pos (and.left Hδ) two_pos},
    split,
    {apply lt.trans,
    apply add_lt_add_left,
    exact div_two_lt_of_pos (and.left Hδ),
    exact Haδ},
    {apply and.right Hδ,
    krewrite [abs_sub, sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg,
             abs_of_pos (div_pos_of_pos_of_pos (and.left Hδ) two_pos)],
    exact div_two_lt_of_pos (and.left Hδ)},
    existsi (b - x) / 2,
    split,
    {apply div_pos_of_pos_of_pos,
    exact sub_pos_of_lt Hxb,
    exact two_pos},
    split,
    {apply add_midpoint Hxb},
    {apply and.right Hδ,
    krewrite [abs_sub, sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg,
            abs_of_pos (div_pos_of_pos_of_pos (sub_pos_of_lt Hxb) two_pos)],
    apply lt_of_lt_of_le,
    apply div_two_lt_of_pos (sub_pos_of_lt Hxb),
    apply sub_left_le_of_le_add,
    apply le_of_not_gt Haδ}}
  end

private lemma sup_near_b {δ : ℝ} (Hpos : 0 < δ)
                (Hgeb : inter_sup a b f + δ / 2 ≥ b) : abs (inter_sup a b f - b) < δ :=
  begin
    apply abs_lt_of_lt_of_neg_lt,
    apply sub_lt_left_of_lt_add,
    apply lt_of_le_of_lt,
    apply Hsupleb,
    apply lt_add_of_pos_right Hpos,
    rewrite neg_sub,
    apply sub_lt_left_of_lt_add,
    apply lt_of_le_of_lt,
    apply Hgeb,
    apply add_lt_add_left,
    apply div_two_lt_of_pos Hpos
  end

private lemma delta_of_lt (Hflt : f (inter_sup a b f) < 0) :
              ∃ δ : ℝ, δ > 0 ∧ inter_sup a b f + δ < b ∧ f (inter_sup a b f + δ) < 0 :=
  if Hlt : inter_sup a b f < b then ex_delta_lt Hflt Hlt else
  begin
    let Heq := eq_of_le_of_ge Hsupleb (le_of_not_gt Hlt),
    apply absurd Hflt,
    apply not_lt_of_ge,
    apply le_of_lt,
    rewrite Heq,
    exact Hb
  end

private theorem sup_fn_interval_aux1 : f (inter_sup a b f) ≥ 0 :=
  have ¬ f (inter_sup a b f) < 0, from
    (suppose  f (inter_sup a b f) < 0,
     obtain δ Hδ, from delta_of_lt this,
     have inter_sup a b f + δ ∈ {x | x < b ∧ f x < 0},
       from and.intro (and.left (and.right Hδ)) (and.right (and.right Hδ)),
     have ¬ inter_sup a b f < inter_sup a b f + δ,
       from not_lt_of_ge (le_sup this Hmem),
     show false, from this (lt_add_of_pos_right (and.left Hδ))),
  le_of_not_gt this

private theorem sup_fn_interval_aux2 : f (inter_sup a b f) ≤ 0 :=
  have ¬ f (inter_sup a b f) > 0, from
  (assume Hfsup : f (inter_sup a b f) > 0,
    obtain δ Hδ, from pos_on_nbhd_of_cts_of_pos Hf Hfsup,
    have ∀ x, x ∈ {x | x < b ∧ f x < 0} → x ≤ inter_sup a b f - δ / 2, from
     (take x, assume Hxset : x ∈ {x | x < b ∧ f x < 0},
      have ¬ x > inter_sup a b f - δ / 2, from
        (assume Hngt,
         have Habs : abs (x - inter_sup a b f) < δ, begin
           rewrite abs_sub,
           apply abs_lt_of_lt_of_neg_lt,
           apply sub_lt_of_sub_lt,
           apply gt.trans,
           exact Hngt,
           apply sub_lt_sub_left,
           exact div_two_lt_of_pos (and.left Hδ),
           rewrite neg_sub,
           apply lt_of_le_of_lt,
           rotate 1,
           apply and.left Hδ,
           apply sub_nonpos_of_le,
           apply le_sup,
           exact Hxset,
           exact Hmem
         end,
         have f x > 0, from and.right Hδ x Habs,
         show false, from (not_lt_of_gt this) (and.right Hxset)),
      le_of_not_gt this),
    have Hle : inter_sup a b f ≤ inter_sup a b f - δ / 2, from sup_le Hinh this,
    show false, from not_le_of_gt
                     (sub_lt_of_pos _ (div_pos_of_pos_of_pos (and.left Hδ) (two_pos))) Hle),
  le_of_not_gt this

private theorem sup_fn_interval : f (inter_sup a b f) = 0 :=
  eq_of_le_of_ge sup_fn_interval_aux2 sup_fn_interval_aux1


private theorem intermediate_value_incr_aux2 : ∃ δ : ℝ, δ > 0 ∧ a + δ < b ∧ f (a + δ) < 0 :=
  begin
    let Hcont := neg_on_nbhd_of_cts_of_neg Hf Ha,
    cases Hcont with δ Hδ,
    {cases em (a + δ < b) with Haδ Haδ,
    existsi δ / 2,
    split,
    {exact div_pos_of_pos_of_pos (and.left Hδ) two_pos},
    split,
    {apply lt.trans,
    apply add_lt_add_left,
    exact div_two_lt_of_pos (and.left Hδ),
    exact Haδ},
    {apply and.right Hδ,
    krewrite [abs_sub, sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg,
             abs_of_pos (div_pos_of_pos_of_pos (and.left Hδ) two_pos)],
    exact div_two_lt_of_pos (and.left Hδ)},
    existsi (b - a) / 2,
    split,
    {apply div_pos_of_pos_of_pos,
    exact sub_pos_of_lt Hab,
    exact two_pos},
    split,
    {apply add_midpoint Hab},
    {apply and.right Hδ,
    krewrite [abs_sub, sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg,
            abs_of_pos (div_pos_of_pos_of_pos (sub_pos_of_lt Hab) two_pos)],
    apply lt_of_lt_of_le,
    apply div_two_lt_of_pos (sub_pos_of_lt Hab),
    apply sub_left_le_of_le_add,
    apply le_of_not_gt Haδ}}
  end

theorem intermediate_value_incr_zero : ∃ c, a < c ∧ c < b ∧ f c = 0 :=
  begin
    existsi inter_sup a b f,
    split,
    {cases intermediate_value_incr_aux2 with δ Hδ,
    apply lt_of_lt_of_le,
    apply lt_add_of_pos_right,
    exact and.left Hδ,
    apply le_sup,
    exact and.right Hδ,
    intro x Hx,
    apply le_of_lt,
    exact and.left Hx},
    split,
    {cases pos_on_nbhd_of_cts_of_pos Hf Hb with δ Hδ,
    apply lt_of_le_of_lt,
    rotate 1,
    apply sub_lt_of_pos,
    exact and.left Hδ,
    rotate_right 1,
    apply sup_le,
    exact exists.intro a (and.intro Hab Ha),
    intro x Hx,
    apply le_of_not_gt,
    intro Hxgt,
    have Hxgt' : b - x < δ, from sub_lt_of_sub_lt Hxgt,
    krewrite [-(abs_of_pos (sub_pos_of_lt (and.left Hx))) at Hxgt', abs_sub at Hxgt'],
    note Hxgt'' := and.right Hδ _ Hxgt',
    exact not_lt_of_ge (le_of_lt Hxgt'') (and.right Hx)},
    {exact sup_fn_interval}
  end

end

theorem intermediate_value_decr_zero {f : ℝ → ℝ} (Hf : continuous f) {a b : ℝ} (Hab : a < b)
        (Ha : f a > 0) (Hb : f b < 0) : ∃ c, a < c ∧ c < b ∧ f c = 0 :=
  begin
    have Ha' : - f a < 0, from neg_neg_of_pos Ha,
    have Hb' : - f b > 0, from neg_pos_of_neg Hb,
    have Hcon : continuous (λ x, - f x), from continuous_neg_of_continuous Hf,
    let Hiv := intermediate_value_incr_zero Hcon Hab Ha' Hb',
    cases Hiv with c Hc,
    existsi c,
    split,
    exact and.left Hc,
    split,
    exact and.left (and.right Hc),
    apply eq_zero_of_neg_eq_zero,
    apply and.right (and.right Hc)
  end

theorem intermediate_value_incr {f : ℝ → ℝ} (Hf : continuous f) {a b : ℝ} (Hab : a < b) {v : ℝ}
        (Hav : f a < v) (Hbv : f b > v) : ∃ c, a < c ∧ c < b ∧ f c = v :=
  have Hav' : f a - v < 0, from sub_neg_of_lt Hav,
  have Hbv' : f b - v > 0, from sub_pos_of_lt Hbv,
  have Hcon : continuous (λ x, f x - v), from continuous_offset_of_continuous Hf _,
  have Hiv : ∃ c, a < c ∧ c < b ∧ f c - v = 0, from intermediate_value_incr_zero Hcon Hab Hav' Hbv',
  obtain c Hc, from Hiv,
  exists.intro c
    (and.intro (and.left Hc) (and.intro (and.left (and.right Hc)) (eq_of_sub_eq_zero (and.right (and.right Hc)))))

theorem intermediate_value_decr {f : ℝ → ℝ} (Hf : continuous f) {a b : ℝ} (Hab : a < b) {v : ℝ}
        (Hav : f a > v) (Hbv : f b < v) : ∃ c, a < c ∧ c < b ∧ f c = v :=
  have Hav' : f a - v > 0, from sub_pos_of_lt Hav,
  have Hbv' : f b - v < 0, from sub_neg_of_lt Hbv,
  have Hcon : continuous (λ x, f x - v), from continuous_offset_of_continuous Hf _,
  have Hiv : ∃ c, a < c ∧ c < b ∧ f c - v = 0, from intermediate_value_decr_zero Hcon Hab Hav' Hbv',
  obtain c Hc, from Hiv,
  exists.intro c
    (and.intro (and.left Hc) (and.intro (and.left (and.right Hc)) (eq_of_sub_eq_zero (and.right (and.right Hc)))))
