#check @array.mk

#eval mk_array 4 1

def v : array nat := @array.mk nat 10 (λ ⟨i, _⟩, i)

#eval array.map (+10) v

def w : array nat :=
(mk_array 9 1).push 3

def f : fin w.sz → nat :=
array.cases_on w (λ _ f, f)

def main1 := f ⟨1, sorry⟩
def main2 := f ⟨9, sorry⟩

#eval main1
#eval main2

#eval (((mk_array 1 1).push 2).push 3).foldl 0 (+)

def array_sum (a : array nat) : nat :=
a.foldl 0 (+)

#eval array_sum (mk_array 10 1)

#exit

#eval (mk_array 10 1).data ⟨1, dec_trivial⟩ + 20
#eval (mk_array 10 1).data ⟨2, dec_trivial⟩
#eval (mk_array 10 3).data ⟨2, dec_trivial⟩
