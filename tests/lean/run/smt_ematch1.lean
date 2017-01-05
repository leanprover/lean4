constant f : nat → nat
axiom fax : ∀ x, f x = x

attribute [ematch] fax

example (a b c : nat) : f a = b → b = f c → a = c :=
begin [smt]
  trace_state,
  ematch
end
