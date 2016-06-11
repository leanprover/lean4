set_option pp.all true

open tactic name list

set_option pp.goal.compact true
set_option pp.binder_types true

#tactic (∀ (p : Prop), p → p → p),
 do
    intro_lst ["_", "H1", "H2"],
    revert "H1",
    trace_state,
    r ← result,
    trace_expr r,
    intro "H3",
    r ← result,
    trace_expr r,
    assumption,
    r ← result,
    trace_expr r,
    return ()

print "====================="

#tactic (∀ (p : Prop), p → p → p),
 do
    intro_lst ["_", "H1", "H2"],
    revert_lst ["H1", "H2"],
    trace_state,
    r ← result,
    trace_expr r,
    intro "H3",
    trace_state,
    trace "------------",
    r ← result,
    trace_expr r,
    (assumption <|> trace "assumption failed"),
    intro "H4",
    assumption,
    trace "------------",
    r ← result,
    trace_expr r,
    return ()

print "====================="

#tactic (∀ (p : Prop), p → p → p),
 do
   intros,
   revert "p",
   trace_state,
   intros,
   assumption,
   r ← result,
   trace_expr r,
   return ()
