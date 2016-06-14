open tactic name list

set_option pp.goal.compact true
set_option pp.binder_types true

example : ∀ (A B : Prop), A → A ∧ B → A → A :=
by do
    intro_lst ["_", "_", "H1", "H2", "H3"],
    trace_state,
    h2 ← get_local "H2",
    infer_type h2 >>= trace_expr,
    h1 ← get_local "H1",
    h3 ← get_local "H3",
    r  : bool ← unify h1 h3,
    trace ("result H1 =?= H3: " + to_string r),
    r  : bool ← unify h2 h3,
    trace ("result H2 =?= H3: " + to_string r),
    assumption,
    trace_state,
    result >>= trace_expr,
    trace "--------------",
    return ()
