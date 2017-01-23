constant f : nat → nat
constant g : nat → nat
axiom Ax : ∀ x, (: f (g x) :) = x

open tactic

meta def add_insts : list (expr × expr) → tactic unit
| []              := skip
| ((inst, pr)::r) := do
  assertv `_einst inst pr,
  add_insts r

meta def ematch_test (h : name) (e : expr) : tactic unit :=
do cc  ← cc_state.mk_using_hs,
   ems ← return $ ematch_state.mk {},
   hlemma ← hinst_lemma.mk_from_decl h,
   (r, cc, ems) ← ematch cc ems hlemma e,
   add_insts r

example (a b c : nat) : f a = b → a = g c → f a ≠ c → false :=
by do
  intros,
  e ← to_expr `(f a),
  ematch_test `Ax e,
  trace_state,
  cc

example (a b c : nat) : f a = b → a = g c → f a = c :=
by do
  intros,
  e ← to_expr `(f a),
  ematch_test `Ax e,
  cc
