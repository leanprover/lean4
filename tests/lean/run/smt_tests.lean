attribute [pre_smt] add_zero zero_add mul_one one_mul

constant p    : nat → nat → Prop
constants a b : nat
constant h    : p (a + 1 * b + 0) (a + b)

set_option trace.app_builder true

open tactic smt_tactic

def ex : p (a + b) (a + b) :=
begin [smt]
  do {
    h ← to_expr `(h),
    t ← infer_type h,
    (new_t, he) ← preprocess t, -- use smt_tactic preprocessor
    new_h ← mk_app `eq.mp [he, h],
    exact new_h
  }
end
