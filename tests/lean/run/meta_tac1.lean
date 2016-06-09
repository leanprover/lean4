set_option pp.all true

open tactic name

#tactic (∀ (p : Prop), p → p),
 do env ← get_env,
    trace "testing",
    return unit.star

#tactic (∀ (p : Prop), p → p),
 do d ← get_decl ("nat" <s> "add"),
    trace_expr (declaration.type d),
    trace "nat.rec type:",
    d ← get_decl ("nat" <s> "rec"),
    trace_expr (declaration.type d),
    return unit.star
