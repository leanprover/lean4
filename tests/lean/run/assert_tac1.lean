open tactic

definition tst1 (a : nat) : a = a :=
by do
   define `x (expr.const `nat []),
   trace_state,
   a ← get_local `a,
   exact a,
   x ← get_local `x,
   mk_app `eq.refl [x] >>= exact

print tst1

definition tst2 (a : nat) : a = a :=
by do
   define `x (expr.const `nat []),
   a ← get_local `a,
   exact a,
   trace "------------",
   trace_state,
   get_local `x >>= revert,
   intro `y,
   trace_state,
   y ← get_local `y,
   mk_app `eq.refl [y] >>= exact

print tst2

definition tst3 (a : nat) : a = a :=
begin
  define x : nat,
  exact a,
  revert x,
  intro y,
  apply eq.refl y
end
