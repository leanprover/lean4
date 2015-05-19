import data.nat
open nat

example (a : nat) : a + 0 = a :=
begin
  induction a using nat.strong_induction_on with a IH,
  cases a,
  reflexivity,
  have aux : a + 0 = a, from IH a (lt.base a),
  rewrite -aux
end
