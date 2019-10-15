def f1 (n : Nat) (i : Int) :=
i + n -- works

def f2 (n : Nat) (i : Int) :=
n + i -- fails can't coerce Int to Nat

def f3 (n : Nat) (i : Int) :=
n + (n + (n + (n + i))) -- nested version of the previous issue

def f4 (n : Nat) (i : Int) :=
n + (n + (n * (n * i))) -- nested version of the previous issue with mixed operators

def f5 (n : Nat) (i : Int) :=
n + (n + (n * (i, i).1)) -- mixed operators and different structures
