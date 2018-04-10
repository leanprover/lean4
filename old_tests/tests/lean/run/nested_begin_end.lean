open tactic

example (p q : Prop) : p ∧ q ↔ q ∧ p :=
by do
  iff_intro   ← mk_const `iff.intro,
  and_intro   ← mk_const `and.intro,
  apply iff_intro,
  solve1 (do
    H ← intro `H,
    apply and_intro,
    mk_app `and.right [H] >>= exact,
    mk_app `and.left [H] >>= exact),
  solve1 (do
    H ← intro `H,
    apply and_intro,
    mk_app `and.right [H] >>= exact,
    mk_app `and.left  [H] >>= exact)
