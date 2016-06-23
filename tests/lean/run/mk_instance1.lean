open tactic

example (a b : nat) : decidable (a = b) :=
by do t ← mk_app "decidable_eq" [expr.const "nat" []],
      /- We had to mark that `i` is an expr because of a limitation of the current elaborator.
         When we write (i a b), the current elaborator only considers the coercion expr.app to function class
         if the type of `i` is known at preprocessing time. This limitation will be removed in the new
         elaborator. -/
      i : expr ← mk_instance t,
      a ← get_local "a",
      b ← get_local "b",
      trace i,
      exact (i a b)

example (a b : nat) : decidable (a = b) :=
by do t ← target,
      i ← mk_instance t,
      trace i,
      exact i

example (a b : nat) : decidable (a = b) :=
by target >>= mk_instance >>= exact
