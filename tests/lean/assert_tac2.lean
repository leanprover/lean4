import data.nat
open nat

example (a b c : nat) : a = 2 → b = 3 → a + b + c = c + 5 :=
begin
  intro h1 h2,
  have H : a + b = 2 + b, by rewrite h1,
  have H : a + b = 2 + 3, by rewrite -h2; exact H,
  have H : a + b = 5, from H,
  rewrite H,
  state,
  rewrite add.comm
end
