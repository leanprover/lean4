/-!
Regression test for #15388: the `[grind hom]` equality and disequality hooks used
`mkEqMP`, which re-infers the type of the E-graph proof and checks it against the
translated fact with `Meta.isDefEq`. After the normalizer unfolds a `let`-bound
literal (`zetaDelta`) and evaluates `m.cpop` to a literal, the stored fact `b = 1#2`
and the hypothesis type `b = m.cpop` are only kernel-definitionally equal, and the
`Meta`-level check failed with an `Application type mismatch`.
-/

example (b : BitVec 2) : let m : BitVec 2 := 1#2; b = m.cpop → b = 1 := by
  intro m h
  grind

-- Disequality hook.
example (b : BitVec 2) : let m : BitVec 2 := 1#2; b ≠ m.cpop → b.toNat ≠ 1 := by
  intro m h
  grind

-- Same, with the literal stated as a hypothesis.
example (m b : BitVec 2) (h : m = 1#2) : b = m.cpop → b = 1 := by
  intro hb
  grind
