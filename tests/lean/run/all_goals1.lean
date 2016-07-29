open tactic

example (a b c : Prop) : a → a :=
by do intro `H,
      a ← get_local `a,
      assert `H1 a,
      assert `H2 a,
      assert `H3 a,
      assert `H4 a,
      assert `H5 a,
      trace_state,
      all_goals assumption,
      trace "--- after all_goals assumption ---",
      trace_result
