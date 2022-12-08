def four1 := double 2
where double (n : Nat) : Nat := 2 * n

def four2 := double 2
where double : Nat → Nat := fun n => 2 * n

def four3 := double 2
where double(n : Nat) : Nat := 2 * n

def four4 := double 2
where double: Nat → Nat := fun n => 2 * n

def four5 := let double(n : Nat) : Nat := 2 * n
             double 2

def four6 := let double: Nat → Nat := fun n => 2 * n
             double 2

def four7 := let rec double: Nat → Nat := fun n => 2 * n
             double 2
