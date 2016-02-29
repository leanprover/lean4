import data.nat
open nat

constant P : nat → Prop

example (Hex : ∃ n, P n) : true :=
  obtain n Hn, from Hex,
  begin
    note Hn2 := Hn,
    exact trivial
  end

example (Hex : ∃ n, P n) : true :=
  obtain n Hn, from Hex,
  begin
    have H : n ≥ 0, from sorry,
    exact trivial
  end
