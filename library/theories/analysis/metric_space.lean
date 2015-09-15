/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Metric spaces.
-/
import data.real.division
open real eq.ops classical

structure metric_space [class] (M : Type) : Type :=
  (dist : M → M → ℝ)
  (dist_self : ∀ x : M, dist x x = 0)
  (eq_of_dist_eq_zero : ∀ {x y : M}, dist x y = 0 → x = y)
  (dist_comm : ∀ x y : M, dist x y = dist y x)
  (dist_triangle : ∀ x y z : M, dist x y + dist y z ≥ dist x z)

namespace metric_space

section metric_space_M
variables {M : Type} [strucM : metric_space M]
include strucM

proposition dist_eq_zero_iff (x y : M) : dist x y = 0 ↔ x = y :=
iff.intro eq_of_dist_eq_zero (suppose x = y, this ▸ !dist_self)

proposition dist_nonneg (x y : M) : 0 ≤ dist x y :=
have dist x y + dist y x ≥ 0, by rewrite -(dist_self x); apply dist_triangle,
have 2 * dist x y ≥ 0, using this,
  by rewrite [-real.one_add_one, right_distrib, +one_mul, dist_comm at {2}]; apply this,
nonneg_of_mul_nonneg_left this two_pos

proposition dist_pos_of_ne {x y : M} (H : x ≠ y) : dist x y > 0 :=
lt_of_le_of_ne !dist_nonneg (suppose 0 = dist x y, H (iff.mp !dist_eq_zero_iff this⁻¹))

proposition eq_of_forall_dist_le {x y : M} (H : ∀ ε, ε > 0 → dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_zero_of_nonneg_of_forall_le !dist_nonneg H)

open nat

definition converges_to_seq (X : ℕ → M) (y : M) : Prop :=
∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → dist (X n) y < ε

-- the same, with ≤ in place of <; easier to prove, harder to use
definition converges_to_seq.intro {X : ℕ → M} {y : M}
    (H : ∀ ⦃ε : ℝ⦄, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → dist (X n) y ≤ ε) :
  converges_to_seq X y :=
take ε, assume epos : ε > 0,
  have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
  obtain N HN, from H e2pos,
  exists.intro N
    (take n, suppose n ≥ N,
      calc
        dist (X n) y ≤ ε / 2 : HN _ `n ≥ N`
                 ... < ε     : div_two_lt_of_pos epos)

notation X `⟶` y `in` `ℕ` := converges_to_seq X y

definition converges_seq [class] (X : ℕ → M) : Prop := ∃ y, X ⟶ y in ℕ

noncomputable definition limit_seq (X : ℕ → M) [H : converges_seq X] : M := some H

proposition converges_to_limit_seq (X : ℕ → M) [H : converges_seq X] :
  (X ⟶ limit_seq X in ℕ) :=
some_spec H

proposition converges_to_seq_unique {X : ℕ → M} {y₁ y₂ : M}
  (H₁ : X ⟶ y₁ in ℕ) (H₂ : X ⟶ y₂ in ℕ) : y₁ = y₂ :=
eq_of_forall_dist_le
  (take ε, suppose ε > 0,
    have e2pos : ε / 2 > 0, from  div_pos_of_pos_of_pos `ε > 0` two_pos,
    obtain N₁ (HN₁ : ∀ {n}, n ≥ N₁ → dist (X n) y₁ < ε / 2), from H₁ e2pos,
    obtain N₂ (HN₂ : ∀ {n}, n ≥ N₂ → dist (X n) y₂ < ε / 2), from H₂ e2pos,
    let N := max N₁ N₂ in
    have dN₁ : dist (X N) y₁ < ε / 2, from HN₁ !le_max_left,
    have dN₂ : dist (X N) y₂ < ε / 2, from HN₂ !le_max_right,
    have dist y₁ y₂ < ε, from calc
      dist y₁ y₂ ≤ dist y₁ (X N) + dist (X N) y₂ : dist_triangle
             ... = dist (X N) y₁ + dist (X N) y₂ : dist_comm
             ... < ε / 2 + ε / 2                 : add_lt_add dN₁ dN₂
             ... = ε                             : add_halves,
    show dist y₁ y₂ ≤ ε, from le_of_lt this)

proposition eq_limit_of_converges_to_seq {X : ℕ → M} (y : M) (H : X ⟶ y in ℕ) :
  y = @limit_seq M _ X (exists.intro y H) :=
converges_to_seq_unique H (@converges_to_limit_seq M _ X (exists.intro y H))

proposition converges_to_seq_constant (y : M) : (λn, y) ⟶ y in ℕ :=
take ε, assume egt0 : ε > 0,
  exists.intro 0
    (take n, suppose n ≥ 0,
      calc
        dist y y = 0 : !dist_self
             ... < ε : egt0)

definition cauchy (X : ℕ → M) : Prop :=
∀ ε : ℝ, ε > 0 → ∃ N, ∀ m n, m ≥ N → n ≥ N → dist (X m) (X n) < ε

proposition cauchy_of_converges_seq (X : ℕ → M) [H : converges_seq X] : cauchy X :=
take ε, suppose ε > 0,
  obtain y (Hy : converges_to_seq X y), from H,
  have e2pos : ε / 2 > 0, from div_pos_of_pos_of_pos `ε > 0` two_pos,
  obtain N₁ (HN₁ : ∀ {n}, n ≥ N₁ → dist (X n) y < ε / 2), from Hy e2pos,
  obtain N₂ (HN₂ : ∀ {n}, n ≥ N₂ → dist (X n) y < ε / 2), from Hy e2pos,
  let N := max N₁ N₂ in
    exists.intro N
      (take m n, suppose m ≥ N, suppose n ≥ N,
        have m ≥ N₁, from le.trans !le_max_left `m ≥ N`,
        have n ≥ N₂, from le.trans !le_max_right `n ≥ N`,
        have dN₁ : dist (X m) y < ε / 2, from HN₁ `m ≥ N₁`,
        have dN₂ : dist (X n) y < ε / 2, from HN₂ `n ≥ N₂`,
        show dist (X m) (X n) < ε, from calc
          dist (X m) (X n) ≤ dist (X m) y + dist y (X n) : dist_triangle
                       ... = dist (X m) y + dist (X n) y : dist_comm
                       ... < ε / 2 + ε / 2               : add_lt_add dN₁ dN₂
                       ... = ε                           : add_halves)

end metric_space_M

section metric_space_M_N
variables {M N : Type} [strucM : metric_space M] [strucN : metric_space N]
include strucM strucN

definition converges_to_at (f : M → N) (y : N) (x : M) :=
∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ x', x ≠ x' ∧ dist x x' < δ → dist (f x') y < ε

notation f `⟶` y `at` x := converges_to_at f y x

definition converges_at [class] (f : M → N) (x : M) :=
∃ y, converges_to_at f y x

noncomputable definition limit_at (f : M → N) (x : M) [H : converges_at f x] : N :=
some H

proposition converges_to_limit_at (f : M → N) (x : M) [H : converges_at f x] :
  (f ⟶ limit_at f x at x) :=
some_spec H

definition continuous_at (f : M → N) (x : M) := converges_to_at f (f x) x

definition continuous (f : M → N) := ∀ x, continuous_at f x

theorem continuous_at_spec {f : M → N} {x : M} (Hf : continuous_at f x)  :
        ∀ ⦃ε⦄, ε > 0 → ∃ δ, δ > 0 ∧ ∀ x', dist x x' < δ → dist (f x') (f x) < ε :=
take ε, suppose ε > 0,
obtain δ Hδ, from Hf this,
exists.intro δ (and.intro
  (and.left Hδ)
  (take x', suppose dist x x' < δ,
   if Heq : x = x' then
     by rewrite [Heq, dist_self]; assumption
   else
     (suffices dist x x' < δ, from and.right Hδ _ (and.intro Heq this),
      this)))

definition image_seq (X : ℕ → M) (f : M → N) : ℕ → N := λ n, f (X n)

theorem image_seq_converges_of_converges [instance] (X : ℕ → M) [HX : converges_seq X] {f : M → N} (Hf : continuous f) :
        converges_seq (image_seq X f) :=
  begin
    cases HX with xlim Hxlim,
    existsi f xlim,
    rewrite ↑converges_to_seq at *,
    intros ε Hε,
    let Hcont := Hf xlim Hε,
    cases Hcont with δ Hδ,
    cases Hxlim (and.left Hδ) with B HB,
    existsi B,
    intro n Hn,
    cases em (xlim = X n),
    rewrite [↑image_seq, a, dist_self],
    assumption,
    rewrite ↑image_seq,
    apply and.right Hδ,
    split,
    exact a,
    rewrite dist_comm,
    apply HB Hn
  end

end metric_space_M_N

end metric_space
