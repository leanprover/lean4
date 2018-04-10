inductive tree
| leaf : tree
| node (left : tree) (val : nat) (right : tree) : tree

constant foo : tree → tree

example (a : tree) : foo a = a :=
begin
  induction a,
  trace_state,
  repeat { admit }
end
