open smt_tactic

example (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
by using_smt $ do
   trace_state,
   a_1 ← tactic.get_local `a_1,
   destruct a_1,
   repeat close
