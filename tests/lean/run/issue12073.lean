-- set_option trace.Meta.injective true
/-!
A mix of propositional and dependent fields
-/
structure Tricky where
  a : Nat
  a' : Nat
  b : 42 < a
  c : Fin a
  d : 23 < c.toNat
  e : a = a'
  f : Fin c.toNat
