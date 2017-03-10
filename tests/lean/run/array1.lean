#check @array.mk

#eval mk_array 4 1

def v : array nat 10 :=
@array.mk nat 10 (λ ⟨i, _⟩, i)

#eval array.map (+10) v

def w : array nat 10 :=
(mk_array 9 1)^.push_back 3

def f : fin 10 → nat :=
array.cases_on w (λ f, f)

#eval f ⟨9, dec_trivial⟩
#eval f ⟨2, dec_trivial⟩

#eval (((mk_array 1 1)^.push_back 2)^.push_back 3)^.foldl 0 (+)

def array_sum {n} (a : array nat n) : nat :=
a^.foldl 0 (+)

#eval array_sum (mk_array 10 1)

#eval (mk_array 10 1)^.data ⟨1, dec_trivial⟩ + 20
#eval (mk_array 10 1)^.data 2
#eval (mk_array 10 3)^.data 2
