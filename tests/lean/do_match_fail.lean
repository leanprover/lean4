open tactic

meta def no_intros : tactic unit :=
do [] ← intros, return ()

example (p q : Prop) : p → q → p :=
begin
  no_intros -- Should fail
end

example (p q : Prop) : p → q → p :=
begin
  intros,
  no_intros,  -- Should work
  assumption
end

example : list nat :=
do l    ← return $ [1, 2, 3],
   h::l ← return l,  -- non-exhaustive set of equations
   return 1

meta example : tactic nat :=
do (a, b) ← return (1, 2), -- Ok
   return a
