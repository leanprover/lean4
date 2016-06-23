import data.nat
open tactic nat decidable

constant nat_has_add1 : has_add nat
constant nat_has_add2 : nat → has_add nat

constant foo (a : nat) : a > 0 → Prop

set_option pp.all true

example (a b : nat)
  (H1 : @add nat nat_has_add1 a b = 0)
  (H2 : @add nat (nat_has_add2 (0 + a + b)) a b = 0)
  (H3 : @add nat nat_has_add1 b (a + b) = 0)
  (H4 : foo (succ (succ (succ zero))) dec_trivial)
  (H5 : foo (succ (succ (succ zero))) sorry)
  : true :=
by do
  h₁ ← get_local "H1" >>= infer_type >>= abstract_weight,
  h₂ ← get_local "H2" >>= infer_type >>= abstract_weight,
  h₃ ← get_local "H3" >>= infer_type >>= abstract_weight,
  h₄ ← get_local "H4" >>= infer_type >>= abstract_weight,
  h₅ ← get_local "H5" >>= infer_type >>= abstract_weight,
  trace $ to_string h₁ + " " + to_string h₂ + " " + to_string h₃,
  trace $ to_string h₄ + " " + to_string h₅,
  get_local "H4" >>= infer_type >>= trace,
  get_local "H5" >>= infer_type >>= trace,
  if h₁ ≠ h₂ then fail "ERROR" else skip,
  if h₁ = h₃ then fail "ERROR" else skip,
  constructor
