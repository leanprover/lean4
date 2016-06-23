open tactic bool

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

example (a b : nat)
  (H1 : ∀ d c : nat, @add nat nat_has_add1 a b = c + d)
  (H2 : ∀ d c : nat, @add nat nat_has_add2 a b = c + d)
  (H3 : ∀ d c : nat, @add nat nat_has_add1 a b = d + d)
  : true :=
by do
  get_local "H1" >>= infer_type >>= abstract_hash >>= trace,
  get_local "H2" >>= infer_type >>= abstract_hash >>= trace,
  H1 ← get_local "H1" >>= infer_type,
  H2 ← get_local "H2" >>= infer_type,
  H3 ← get_local "H3" >>= infer_type,
  abstract_eq H1 H2 >>= trace,
  abstract_eq H1 H3 >>= trace,
  abstract_eq H1 H2 >>= (λ b, when (b = ff) (fail "ERROR1")),
  abstract_eq H1 H3 >>= (λ b, when (b = tt) (fail "ERROR2")),
  constructor
