import logic data.nat.sub algebra.relation data.prod

open nat relation relation.iff_ops prod
open decidable
open eq.ops

namespace nat

-- A general recursion principle
-- -----------------------------
--
-- Data:
--
--   dom, codom : Type
--   default : codom
--   measure : dom → ℕ
--   rec_val : dom → (dom → codom) → codom
--
-- and a proof
--
--   rec_decreasing : ∀m, m ≥ measure x, rec_val x f = rec_val x (restrict f m)
--
-- ... which says that the recursive call only depends on f at values with measure less than x,
-- in the sense that changing other values to the default value doesn't change the result.
--
-- The result is a function f = rec_measure, satisfying
--
--   f x = rec_val x f

definition restrict {dom codom : Type} (default : codom) (measure : dom → ℕ) (f : dom → codom)
    (m : ℕ) (x : dom) :=
if measure x < m then f x else default

theorem restrict_lt_eq {dom codom : Type} (default : codom) (measure : dom → ℕ) (f : dom → codom)
    (m : ℕ) (x : dom) (H : measure x < m) :
  restrict default measure f m x = f x :=
if_pos H

theorem restrict_not_lt_eq {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (f : dom → codom) (m : ℕ) (x : dom) (H : ¬ measure x < m) :
  restrict default measure f m x = default :=
if_neg H

definition rec_measure_aux {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom) : ℕ → dom → codom :=
nat.rec (λx, default) (λm g x, if measure x < succ m then rec_val x g else default)

definition rec_measure {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom) (x : dom) : codom :=
rec_measure_aux default measure rec_val (succ (measure x)) x

attribute decidable [multiple-instances]

theorem rec_measure_aux_spec {dom codom : Type} (default : codom) (measure : dom → ℕ)
    (rec_val : dom → (dom → codom) → codom)
    (rec_decreasing : ∀g1 g2 x, (∀z, measure z < measure x → g1 z = g2 z) →
        rec_val x g1 = rec_val x g2)
    (m : ℕ) :
  let f' := rec_measure_aux default measure rec_val in
  let f := rec_measure default measure rec_val in
  ∀x, f' m x = restrict default measure f m x :=
let f' := rec_measure_aux default measure rec_val in
let f  := rec_measure default measure rec_val in
nat.case_strong_induction_on m
  (take x,
    have H1 : f' 0 x = default, from rfl,
    have H2 : ¬ measure x < 0, from !not_lt_zero,
    have H3 : restrict default measure f 0 x = default, from if_neg H2,
    show f' 0 x = restrict default measure f 0 x, from H1 ⬝ H3⁻¹)
  (take m,
    assume IH: ∀n, n ≤ m → ∀x, f' n x = restrict default measure f n x,
    take x : dom,
    show f' (succ m) x = restrict default measure f (succ m) x, from
      by_cases -- (measure x < succ m)
        (assume H1 : measure x < succ m,
          assert H2a : ∀z, measure z < measure x → f' m z = f z,
          proof
            take z,
              assume Hzx : measure z < measure x,
              calc
                f' m z = restrict default measure f m z : IH m !le.refl z
                  ... = f z : !restrict_lt_eq (lt_of_lt_of_le Hzx (le_of_lt_succ H1))
          ∎,
          have H2 : f' (succ m) x = rec_val x f,
          proof
            calc
              f' (succ m) x = if measure x < succ m then rec_val x (f' m) else default : rfl
                ... = rec_val x (f' m) : if_pos H1
                ... = rec_val x f : rec_decreasing (f' m) f x H2a
          ∎,
          let m' := measure x in
          assert H3a : ∀z, measure z < m' → f' m' z = f z,
          proof
            take z,
              assume Hzx : measure z < measure x,
              calc
                f' m' z = restrict default measure f m' z : IH _ (le_of_lt_succ H1) _
                  ... = f z : !restrict_lt_eq Hzx
          qed,
          have H3 : restrict default measure f (succ m) x = rec_val x f,
          proof
            calc
              restrict default measure f (succ m) x = f x : if_pos H1
                ... = f' (succ m') x : !eq.refl
                ... = if measure x < succ m' then rec_val x (f' m') else default : rfl
                ... = rec_val x (f' m') : if_pos !lt_succ_self
                ... = rec_val x f : rec_decreasing _ _ _ H3a
          qed,
          show f' (succ m) x = restrict default measure f (succ m) x,
            from H2 ⬝ H3⁻¹)
        (assume H1 : ¬ measure x < succ m,
          have H2 : f' (succ m) x = default, from
            calc
              f' (succ m) x = if measure x < succ m then rec_val x (f' m) else default : rfl
                ... = default : if_neg H1,
          have H3 : restrict default measure f (succ m) x = default,
            from if_neg H1,
          show f' (succ m) x = restrict default measure f (succ m) x,
            from H2 ⬝ H3⁻¹))

end nat
