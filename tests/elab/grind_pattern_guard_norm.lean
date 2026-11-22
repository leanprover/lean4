/-!
The terms in `grind_pattern` guards are normalized like the patterns, because they are compared
with terms that `grind` has normalized. The `Sym.simp` normalizer writes `a + b * c` as
`b * c + a`, so an unnormalized guard `_ + _ * _` did not block that instance.
-/

opaque r : Nat → Nat → Nat
axiom r_eq (s m : Nat) : r s m = m

grind_pattern r_eq => r s m where
  s =/= _ + _ * _

-- The guard blocks the instance, so `grind` fails.
example (a b c : Nat) : r (a + b * c) 0 = 0 := by
  fail_if_success grind
  exact r_eq _ _

example (a : Nat) : r a 0 = 0 := by grind

-- The guard is normalized when `grind_pattern` is elaborated, so the option is set first.
set_option backward.grind.normalizer false

opaque r' : Nat → Nat → Nat
axiom r'_eq (s m : Nat) : r' s m = m

grind_pattern r'_eq => r' s m where
  s =/= _ + _ * _

example (a b c : Nat) : r' (a + b * c) 0 = 0 := by
  fail_if_success grind
  exact r'_eq _ _

example (a : Nat) : r' a 0 = 0 := by grind
