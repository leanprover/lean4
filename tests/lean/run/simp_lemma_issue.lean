universe variables u

def ex {α : Type u} [comm_semiring α] (a : α) : 0 + a = a :=
zero_add a

local attribute [-simp] zero_add add_zero
attribute [simp] ex

example (a b : nat) : 0 + 0 + a = a :=
by simp

local attribute [-ematch] zero_add add_zero
attribute [ematch] ex

example (a b : nat) : 0 + 0 + a = a :=
by using_smt $ smt_tactic.eblast
