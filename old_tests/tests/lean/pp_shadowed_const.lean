def f : Π (x : nat) (b : bool), bool = bool := λ bool, _

def g (heq : 1 == 1) := heq.symm
#print g

open nat
def h1 : Π n : nat, pred n = n := λ n, _
def h2 : Π n : nat, pred n = n := λ pred, _
def h3 : Π n m : nat, pred n = m := λ pred nat, _
