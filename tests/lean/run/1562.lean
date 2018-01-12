meta constant term : Type
meta constant smt2.builder.int_const : int -> term

meta constant smt2_state : Type

@[reducible] meta def smt2_m (α : Type) :=
state_t smt2_state tactic α

meta instance tactic_to_smt2_m (α : Type) : has_coe (tactic α) (smt2_m α) :=
⟨ fun tc, ⟨fun s, do res ← tc, return (res, s)⟩ ⟩

meta def reflect_arith_formula : expr → smt2_m term
| `(has_zero.zero) := smt2.builder.int_const <$> tactic.eval_expr int `(has_zero.zero int)
| a := tactic.fail "foo"
