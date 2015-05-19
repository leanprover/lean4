import data.vector
open vector

set_option pp.implicit true

attribute and.rec_on [recursor 4]

example (a b : Prop) (h : a ∧ b) : a :=
begin
  induction h using and.rec_on with ha hb,
  exact ha
end

example (A : Type) (n : nat) (v w : vector A n) (h : v = w) : w = v :=
begin
  induction v with n a t r,
  rewrite -h,
  rewrite -h
end
