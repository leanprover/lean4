#print [simp] default

constant addz (a : nat) : 0 + a = a
attribute [simp] addz

open tactic

def ex : (λ a b : nat, 0 + a) = (λ a b, a) :=
by simp

#print ex
