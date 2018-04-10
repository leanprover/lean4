open nat
open tactic

meta def match_le (e : expr) : tactic (expr × expr) :=
match expr.is_le e with
| (some r) := return r
| none     := tactic.fail "expression is not a leq"
end

meta def nat_lit_le : tactic unit := do
  (base_e, bound_e) ← tactic.target >>= match_le,
  base  ← tactic.eval_expr ℕ base_e,
  skip

example : 17 ≤ 555555 :=
begin
  nat_lit_le,
  admit
end

example : { k : ℕ // k ≤ 555555 } :=
begin
  refine subtype.mk _ _,
  exact 17,
  target >>= trace,
  trace_state,
  nat_lit_le,
  admit
end

set_option pp.instantiate_mvars false

example : { k : ℕ // k ≤ 555555 } :=
begin
  refine subtype.mk _ _,
  exact 17,
  target >>= trace,
  trace_state,
  nat_lit_le,
  admit
end
