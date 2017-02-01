open tactic

set_option pp.binder_types true
noncomputable definition foo (A : Type) : A → A :=
sorry

example (a : nat) (H : foo unit () = ()) : true :=
by do
  (lhs, rhs) ← get_local `H >>= infer_type >>= match_eq ,
  get_spec_subsingleton_info lhs >>= trace,
  trace "-----------",
  trace "ite information:",
  c ← mk_const `ite, get_fun_info c >>= trace,
  trace "eq.rec information:",
  c ← mk_const `eq.rec, get_fun_info c >>= trace,
  trace "and.intro information:",
  c ← mk_const `and.intro, get_fun_info c >>= trace,
  mk_const `trivial >>= exact
