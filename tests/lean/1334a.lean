inductive nlist : Type
| atom : nlist
| mk : list nlist → nlist

open nlist list

def fn : nlist → nlist
| (mk l) := mk []
| _      := atom

check fn.equations._eqn_1
check fn.equations._eqn_2
