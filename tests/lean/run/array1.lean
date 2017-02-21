check @array.mk

vm_eval mk_array 4 1

def v : array nat 10 :=
@array.mk nat 10 (λ ⟨i, _⟩, i)

vm_eval array.map (+10) v

def w : array nat 10 :=
(mk_array 9 1)^.push_back 3

def f : fin 10 → nat :=
array.cases_on w (λ f, f)

vm_eval f ⟨9, dec_trivial⟩
vm_eval f ⟨2, dec_trivial⟩

vm_eval (((mk_array 1 1)^.push_back 2)^.push_back 3)^.foldl 0 (+)

def array_sum {n} (a : array nat n) : nat :=
a^.foldl 0 (+)

vm_eval array_sum (mk_array 10 1)

vm_eval (mk_array 10 1)^.data ⟨1, dec_trivial⟩
