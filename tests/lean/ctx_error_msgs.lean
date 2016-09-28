open tactic

set_option pp.locals_full_names true

example (f : nat) (a : nat) : true :=
by do
   f ← get_local `f,
   a ← get_local `a,
   infer_type (expr.app f a) >>= trace,
   constructor

example (a : nat) : true :=
by do
   a ← get_local `a,
   clear a,
   infer_type a >>= trace,
   constructor

example (a : nat) : true :=
by do
   infer_type (expr.const `eq []) >>= trace,
   constructor

example (a : nat) : true :=
by do
   l ← return $ level.zero,
   infer_type (expr.const `eq [l, l]) >>= trace,
   constructor
