attribute [pre_smt] add_zero zero_add mul_one one_mul

constant p    : nat → nat → Prop
constants a b : nat
constant h    : p (a + 1 * b + 0) (a + b)

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

def foo : nat → nat
| 0     := 0
| (n+1) := 2*n

example (n : nat) : n = 0 → foo (n+1) = 2*0 :=
begin [smt]
  add_lemma [mul_zero, zero_mul],
  add_eqn_lemmas foo,
  ematch
end

example (n : nat) : n = 0 → foo (n+1) = 2*0 :=
begin [smt]
  ematch_using [foo, mul_zero, zero_mul],
end

example (n : nat) : n = 0 → foo n = 0 :=
begin [smt]
  add_eqn_lemmas foo
end

def boo : nat → nat
| 0     := 1
| (n+1) :=
  match foo n with
  | 0 := 2
  | _ := 3
  end

example (n : nat) : n = 0 → boo (n+1) = 2 :=
begin [smt]
  add_eqn_lemmas boo foo,
  ematch,
end

example (n : nat) : n = 0 → boo (n+1) = 2 :=
begin [smt]
  ematch_using [boo, foo]
end

def r (x : nat) := x

example (n : nat) : n = 0 → boo (n+1) = r 2 :=
begin [smt]
  add_eqn_lemmas boo foo r,
  (smt_tactic.get_lemmas >>= smt_tactic.trace),
  ematch,
end

example (a b : nat) : a = 0 → b = a → b = 0 :=
begin [smt]
  try { trace "hello", smt_tactic.failed },
end

set_option trace.smt true

example (n : nat) : n = 0 → boo (n+1) = r 2 :=
begin [smt]
  add_eqn_lemmas boo foo r,
  ematch,
end
