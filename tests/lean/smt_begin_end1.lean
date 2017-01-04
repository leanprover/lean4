constant p : nat → nat → Prop
constant f : nat → nat
axiom pf (a : nat) : p (f a) (f a) → p a a

example (a b c : nat) : a = b → p (f a) (f b) → p a b :=
begin [smt]
  assert h : p (f a) (f a),
  trace_state,
  add_fact (pf _ h)
end

example (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → false :=
begin [smt]
   by_cases p,
end
