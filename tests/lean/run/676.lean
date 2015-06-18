import data.nat
open nat

inductive foo : Prop :=
mk : ∀ {a : nat}, a > 0 → foo

example (b : nat) (h : b > 1) : foo :=
begin
  fconstructor,
  exact b,
  exact lt_of_succ_lt h
end
