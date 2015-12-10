import data.nat
open algebra

example (a b : Prop) : a → b → a ∧ b :=
begin
  intro Ha, intro Hb,
  let Ha' := Ha,
  let Hb' := Hb,
  let aux := and.intro Ha Hb,
  exact aux
end

open nat

example (a b : nat) : a > 0 → b > 0 → a + b + 0 > 0 :=
begin
  intro agt0, intro bgt0,
  let H := add_pos agt0 bgt0,
  change a + b > 0,
  exact H
end
