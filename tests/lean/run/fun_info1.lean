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
  mk_const `ite >>= get_fun_info >>= trace,
  trace "eq.rec information:",
  mk_const `eq.rec >>= get_fun_info >>= trace,
  trace "and.intro information:",
  mk_const `and.intro >>= get_fun_info >>= trace,
  mk_const `trivial >>= exact
