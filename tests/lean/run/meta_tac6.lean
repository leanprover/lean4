import data.list
open tactic name list

set_option pp.goal.compact true
set_option pp.binder_types true

example : ∀ (A B : Prop), A → A ∧ B → A → A :=
by do
    intro_lst ["_", "_", "H1", "H2", "H3"],
    n : nat ← num_goals,
    ctx : list expr ← local_context,
    trace "Context: ",
    repeat ctx (λ e,
      do t ← infer_type e,
         fmt₁ ← format_expr e,
         fmt₂ ← format_expr t,
         trace_fmt $ fmt₁ + to_fmt " : " + fmt₂),
    trace "----------",
    trace ("num: " + to_string n),
    trace_state,
    clear "H3",
    (do {get_local "H3", return ()} <|> trace "get_local failed"),
    trace_state,
    assumption,
    n : nat ← num_goals,
    trace ("num: " + to_string n),
    return ()
