open tactic
example : true :=
by do
  let n : expr  := `(nat),
  let t : expr  := `(nat → nat),
  m ← mk_meta_var t,
  let em : expr := (expr.lam `x binder_info.default n (expr.app m (expr.var 0))),
  /- The unification constraint
        ?m =?= (fun x, ?m x)
     should work.
  -/
  unify m em,
  constructor

example : true :=
by do
  let n : expr  := `(nat),
  let t : expr  := `(nat → nat),
  m ← mk_meta_var t,
  let em : expr := (expr.lam `x binder_info.default n (expr.app m (expr.var 0))),
  /- The unification constraint
        ?m =?= (fun x, ?m x)
     should work.
  -/
  unify em m,
  constructor
