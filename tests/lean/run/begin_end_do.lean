open tactic

example (a b c : nat) (p : nat → Prop) (f : nat → nat → nat) : p (f (f a a) (f b c)) :=
begin
  do { [x, y, z] ← match_target_subexpr `(λ x y z, f x (f y z)) | failed,
       trace x, trace y, trace z, trace "------------"},
  exact sorry
end
