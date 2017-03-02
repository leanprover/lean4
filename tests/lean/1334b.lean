inductive term : Type
| var  : nat → term
| app  : list term → term
| cnst : string → term

def var_of : term → option nat
| (term.var n) := some n
| _            := none

check var_of.equations._eqn_1
check var_of.equations._eqn_2
check var_of.equations._eqn_3

def list_of : term → list term
| (term.app ts) := ts
| _             := []

check list_of.equations._eqn_1
check list_of.equations._eqn_2
check list_of.equations._eqn_3
