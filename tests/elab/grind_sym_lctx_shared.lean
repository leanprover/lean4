/-!
`grind` must share the value of a let-variable in the local context before the `Sym.simp`
normalizer unfolds it. Otherwise `Sym.Arith.classify?`, which caches by pointer, classifies `Nat`
as a second semiring, and the ring proof panics in `CommRing.Proof.mkSemiringContext`.
-/

set_option backward.grind.normalizer false

example (a b c : Nat) (h : a * b = c) : let x := a * b; x = c := by
  intro x; grind
