open tactic name list

set_option pp.goal.compact true
set_option pp.binder_types true

example : ∀ (A B : Prop), A → A ∧ B → A → A :=
by do
    intro_lst [`_, `_, `H1, `H2, `H3],
    trace_state,
    h2 ← get_local `H2,
    infer_type h2 >>= trace,
    h1 ← get_local `H1,
    h3 ← get_local `H3,
    unify h1 h3,
    (unify h2 h3 <|> trace "fail to unify H2 =?= H3"),
    assumption,
    trace_state,
    result >>= trace,
    trace "--------------",
    return ()
