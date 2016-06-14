set_option pp.all true

open tactic name list

set_option pp.goal.compact true
set_option pp.binder_types true

example : ∀ (p : Prop), p → p :=
by do env ← get_env,
      trace "testing",
      intros,
      assumption

example : ∀ (p : Prop), p → p → p :=
by do d ← get_decl ("nat" <s> "add"),
    trace_expr (declaration.type d),
    trace "nat.rec type:",
    d ← get_decl ("nat" <s> "rec"),
    trace_expr (declaration.type d),
    trace_state,
    r ← result,
    trace_expr r,
    intro_lst ["_", "H1", "H2"],
    trace "-----------",
    trace_result,
    trace "-----------",
    trace_state,
    assumption,
    trace "-----------",
    trace_result
