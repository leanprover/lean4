open tactic

constant nat_has_add1 : has_add nat
constant nat_has_add2 : has_add nat

example (a b : nat)
  (H1 : @add nat nat_has_add1 a b = 0)
  (H2 : @add nat nat_has_add2 a b = 0)
  (H3 : @add nat nat_has_add1 b a = 0)
  : true :=
by do
  h₁ ← get_local "H1" >>= infer_type >>= abstract_hash,
  h₂ ← get_local "H2" >>= infer_type >>= abstract_hash,
  h₃ ← get_local "H3" >>= infer_type >>= abstract_hash,
  trace $ to_string h₁ + " " + to_string h₂ + " " + to_string h₃,
  if h₁ ≠ h₂ then fail "ERROR" else skip,
  if h₁ = h₃ then fail "UNEXPECTED" else skip,
  constructor
