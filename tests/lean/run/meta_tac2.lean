set_option pp.all true

open tactic name list

set_option pp.goal.compact true
set_option pp.binder_types true
set_option pp.delayed_abstraction true

example : ∀ (p : Prop), p → p → p :=
by do
    intro_lst [`_, `H1, `H2],
    trace_state,
    trace_result,
    trace "---------",
    get_local `H1 >>= revert,
    trace_state,
    trace_result,
    intro `H3,
    trace_result,
    assumption,
    trace_result,
    return ()

#print "====================="

example : ∀ (p : Prop), p → p → p :=
by do
    intro_lst [`_, `H1, `H2],
    H1 ← get_local `H1, H2 ← get_local `H2,
    revert_lst [H1, H2],
    trace_state,
    trace_result,
    intro `H3,
    trace_state,
    trace "------------",
    trace_result,
    (assumption <|> trace "assumption failed"),
    intro `H4,
    assumption,
    trace "------------",
    trace_result,
    return ()

#print "====================="

example : ∀ (p : Prop), p → p → p :=
by do
   intros,
   get_local `p >>= revert,
   trace_state,
   trace_result,
   trace "----------",
   intro `p,
   trace_state,
   trace_result,
   trace "----------",
   intro_lst [`H1, `H2],
   assumption,
   trace_result,
   return ()
