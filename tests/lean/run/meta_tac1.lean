set_option pp.all true

open tactic name list

set_option pp.goal.compact true
set_option pp.binder_types true

#tactic (∀ (p : Prop), p → p),
 do env ← get_env,
    trace "testing",
    return ()

#tactic (∀ (p : Prop), p → p → p),
 do d ← get_decl ("nat" <s> "add"),
    trace_expr (declaration.type d),
    trace "nat.rec type:",
    d ← get_decl ("nat" <s> "rec"),
    trace_expr (declaration.type d),
    trace_state,
    r ← result,
    trace_expr r,
    intro_lst ["_", "H1", "H2"],
    trace "-----------",
    r ← result,
    trace_expr r,
    trace "-----------",
    trace_state,
    return ()
