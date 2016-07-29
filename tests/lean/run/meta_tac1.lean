set_option pp.all true

open tactic list

set_option pp.goal.compact true
set_option pp.binder_types true

example : ∀ (p : Prop), p → p :=
by do env ← get_env,
      trace "testing",
      intros,
      assumption

example : ∀ (p : Prop), p → p → p :=
by do d ← get_decl $ `nat.add,
    trace $ declaration.type d,
    trace "nat.rec type:",
    d ← get_decl $ `nat.rec,
    trace $ declaration.type d,
    trace_state,
    r ← result,
    trace r,
    intro_lst [`_, `H1, `H2],
    trace "-----------",
    trace_result,
    trace "-----------",
    trace_state,
    assumption,
    trace "-----------",
    trace_result
