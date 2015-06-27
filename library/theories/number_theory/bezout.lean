/-
Copyright (c) 2015 William Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Peterson, Jeremy Avigad

Extended gcd, Bezout's theorem, chinese remainder theorem.
-/
import data.nat.div data.int
open nat int
open eq.ops well_founded decidable prod

private definition pair_nat.lt : ℕ × ℕ → ℕ × ℕ → Prop := measure pr₂
private definition pair_nat.lt.wf : well_founded pair_nat.lt := intro_k (measure.wf pr₂) 20
local attribute pair_nat.lt.wf [instance]
local infixl `≺`:50 := pair_nat.lt

private definition gcd.lt.dec (x y₁ : ℕ) : (succ y₁, x mod succ y₁) ≺ (x, succ y₁) :=
!nat.mod_lt (succ_pos y₁)

private definition egcd_rec_f (z : ℤ) : ℤ → ℤ → ℤ × ℤ := λ s t, (t, s - t * z)

definition egcd.F : Π (p₁ : ℕ × ℕ), (Π p₂ : ℕ × ℕ, p₂ ≺ p₁ → ℤ × ℤ) → ℤ × ℤ
| (x, y) := nat.cases_on y
              (λ f, (1, 0) )
              (λ y₁ (f : Π p₂, p₂ ≺ (x, succ y₁) → ℤ × ℤ),
                let bz := f (succ y₁, x mod succ y₁) !gcd.lt.dec in
                prod.cases_on bz (egcd_rec_f (x div succ y₁)))

definition egcd (x y : ℕ) := fix egcd.F (pair x y)

theorem egcd_zero (x : ℕ) : egcd x 0 = (1, 0) :=
well_founded.fix_eq egcd.F (x, 0)

theorem egcd_succ (x y : ℕ) :
  egcd x (succ y) = prod.cases_on (egcd (succ y) (x mod succ y)) (egcd_rec_f (x div succ y)) :=
well_founded.fix_eq egcd.F (x, succ y)

theorem egcd_of_pos (x : ℕ) {y : ℕ} (ypos : y > 0) :
  let erec := egcd y (x mod y), u := pr₁ erec, v := pr₂ erec in
    egcd x y = (v, u - v * (x div y)) :=
obtain y' (yeq : y = succ y'), from exists_eq_succ_of_pos ypos,
by rewrite [yeq, egcd_succ, -prod.eta (egcd _ _)]

theorem egcd_prop (x y : ℕ) : (pr₁ (egcd x y)) * x + (pr₂ (egcd x y)) * y = gcd x y :=
gcd.induction x y
  (take m, by rewrite [egcd_zero, ▸*, int.mul_zero, int.one_mul])
  (take m n,
    assume npos : 0 < n,
    assume IH,
    begin
      let H := egcd_of_pos m npos, esimp at H,
      rewrite [H, ▸*, gcd_rec, -IH, add.comm (#int _ * _), -of_nat_mod, ↑modulo],
      rewrite [*int.mul_sub_right_distrib, *int.mul_sub_left_distrib, *mul.left_distrib],
      rewrite [sub_add_eq_add_sub, *sub_eq_add_neg, int.add.assoc, of_nat_div, *int.mul.assoc]
    end)

theorem Bezout (x y : ℕ) : ∃ a b : ℤ, a * x + b * y = gcd x y :=
exists.intro _ (exists.intro _ (egcd_prop x y))
