tactic_notation `foo` A := tactic.id

example (a : nat) : a = a :=
begin
  foo (10:nat),
  reflexivity
end
