def g {n m : nat} (v : array nat (n + m)) : array nat (m + n) :=
eq.rec_on (add_comm n m) v -- Worked before

def f {n m : nat} (v : array nat (n + m)) : array nat (m + n) :=
eq.cases_on (add_comm n m) v -- eq.cases_on was not being erased
