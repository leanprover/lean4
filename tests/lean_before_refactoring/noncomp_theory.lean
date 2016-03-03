import data.real
open real

definition f (a b : real) := (a + a) / b -- ERROR f is noncomputable

noncomputable definition f (a b : real) := (a + a) / b -- ERROR f is noncomputable

noncomputable theory

definition g (a b : real) := (a + a) / b

definition h (a b : real) := (a - a) / b

definition f₂ (a b : real) := (a * a) / b

definition r (a : nat) := a

print g -- g is still marked as noncomputable

print r
