open tactic name list

set_option pp.goal.compact true
set_option pp.binder_types true

#tactic (∀ (A B : Prop), A → A ∧ B → A → A),
 do
    intro_lst ["_", "_", "H1", "H2", "H3"],
    trace_state,
    clear "H3",
    (do {get_local "H3", skip} <|> trace "get_local failed"),
    trace_state,
    assumption,
    r ← result,
    trace_expr r,
    return ()
