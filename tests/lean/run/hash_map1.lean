import data.hash_map

@[reducible]
def nat2string := hash_map nat (λ _, string)

def mk_nat2string : nat2string :=
mk_hash_map (λ n, n)

def m1 : nat2string :=
mk_nat2string^.insert 1 "hello"

def m2 : nat2string :=
(m1^.insert 2 "world")^.insert 3 "test"

vm_eval m1^.contains 1

vm_eval m2

vm_eval m2^.insert 1 "foo"

vm_eval m2^.size

vm_eval m2^.find 1

vm_eval m2^.find 10

vm_eval m2^.erase 10

vm_eval m2^.erase 2
