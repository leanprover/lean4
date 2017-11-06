def g {n m : nat} (v : array (n + m) nat) : array (m + n) nat :=
eq.rec_on (add_comm n m) v -- Worked before

def f {n m : nat} (v : array (n + m) nat) : array (m + n) nat :=
eq.cases_on (add_comm n m) v -- eq.cases_on was not being erased
