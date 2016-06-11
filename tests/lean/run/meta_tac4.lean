open tactic name list

definition foo (a : nat) := a + 1 > 0
definition boo [reducible] (a : nat) := a + 1 > 0

#tactic (∀ (a b : nat), foo a → boo a → a + 1 > 0 → foo a),
 do
    intro_lst ["_", "_", "H1", "H2", "H3"],
    trace_state,
    h1 ← get_local_type "H1",
    h2 ← get_local_type "H2",
    h3 ← get_local_type "H3",
    r : bool ← unify h1 h2,
    trace ("result typeof(H1) =?= typeof(H2): " + to_string r),
    r : bool ← unify h2 h3,
    trace ("result typeof(H2) =?= typeof(H3): " + to_string r),
    r : bool ← unify h1 h3,
    trace ("result typeof(H1) =?= typeof(H3): " + to_string r),
    r : bool ← unify_core h1 h2 transparency.reducible,
    trace ("result typeof(H1) =?= typeof(H2) (reducible only): " + to_string r),
    r : bool ← unify_core h2 h3 transparency.reducible,
    trace ("result typeof(H2) =?= typeof(H3) (reducible only): " + to_string r),
    r : bool ← unify_core h1 h3 transparency.reducible,
    trace ("result typeof(H1) =?= typeof(H3) (reducible only): " + to_string r),
    return ()
