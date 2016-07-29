open tactic name list

set_option pp.goal.compact true
set_option pp.beta false
set_option pp.binder_types true

example : ∀ (A B : Prop), A → A ∧ B → A → A ∧ B :=
by do
    intro_lst [`_, `_, `H1, `H2, `H3],
    trace_state,
    rename `H2 `H5,
    trace_state,
    r ← get_local_type `H5,
    trace r,
    trace "----------",
    assumption,
    trace_state,
    r ← result,
    trace r,
    return ()
