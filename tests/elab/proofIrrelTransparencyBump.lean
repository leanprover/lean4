module

/-!
Proof-irrelevance checks in `isDefEq` compare the types of the two proofs. This comparison bumps
transparency to `.implicit` — mirroring the bump applied when comparing implicit arguments — so
`[implicit_reducible]` definitions unfold even when the surrounding tactic runs at `.reducible`.
The backward-compatibility option `backward.isDefEq.proofIrrelBump := false` disables the bump.
-/

opaque P : Prop

@[implicit_reducible]
def Q := P

/-! With the bump (the default), the types `P` and `Q` are compared at `.implicit` transparency,
where `Q` unfolds. -/

#guard_msgs in
example (p : P) (q : Q) : p = q := by
  with_reducible apply_rfl

/-! Without the bump, the types are compared at the caller's transparency (`.reducible` here),
where `Q` does not unfold. -/

/--
error: Tactic `rfl` failed: The left-hand side
  p
is not definitionally equal to the right-hand side
  q

p : P
q : Q
⊢ p = q
-/
#guard_msgs in
set_option backward.isDefEq.proofIrrelBump false in
example (p : P) (q : Q) : p = q := by
  with_reducible apply_rfl
