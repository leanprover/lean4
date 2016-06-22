open tactic

example (a : nat) : true :=
by do
  trace "ite information:",
  mk_const "ite" >>= get_fun_info >>= trace_fmt ∘ to_fmt,
  trace "eq.rec information:",
  mk_const ("eq" <.> "rec") >>= get_fun_info >>= trace_fmt ∘ to_fmt,
  trace "and.intro information:",
  mk_const ("and" <.> "intro") >>= get_fun_info >>= trace_fmt ∘ to_fmt,
  mk_const "trivial" >>= exact
