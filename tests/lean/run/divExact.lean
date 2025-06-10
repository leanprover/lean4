#guard Nat.divExact 4 2 (by decide) == 2
#guard Nat.divExact 0 0 (by decide) == 0
#guard Nat.divExact 0 2 (by decide) == 0
#guard Nat.divExact 0 (2 ^ 100) (by decide) == 0
#guard Nat.divExact (2 ^ 100) (2 ^ 100) (by decide) == 1
#guard Nat.divExact (2 ^ 100) 4 (by decide) == 2 ^ 98
#guard Nat.divExact (3 ^ 200) (3 ^ 100) (by decide) == 3 ^ 100
#guard Nat.divExact (2 ^ 100) (2 ^ 60) (by decide) == 2 ^ 40

#guard Int.divExact 4 2 (by decide) == 2
#guard Int.divExact 0 0 (by decide) == 0
#guard Int.divExact 0 2 (by decide) == 0
#guard Int.divExact 0 (2 ^ 100 : Nat) (by decide) == 0
#guard Int.divExact (2 ^ 100 : Nat) (2 ^ 100 : Nat) (by decide) == 1
#guard Int.divExact (2 ^ 100 : Nat) 4 (by decide) == 2 ^ 98
#guard Int.divExact (3 ^ 200 : Nat) (3 ^ 100 : Nat) (by decide) == 3 ^ 100

#guard Int.divExact 4 (-2) (by decide) == -2
#guard Int.divExact (-8) (-2) (by decide) == 4
#guard Int.divExact 0 (-2) (by decide) == 0
#guard Int.divExact 0 (-(2 ^ 100 : Nat)) (by decide) == 0
#guard Int.divExact (2 ^ 100 : Nat) (-(2 ^ 100 : Nat)) (by decide) == -1
#guard Int.divExact (-(3 ^ 200 : Nat)) (-(3 ^ 100 : Nat)) (by decide) == 3 ^ 100
#guard Int.divExact (-(3 ^ 100 : Nat)) 3 (by decide) == -3 ^ 99
#guard Int.divExact (-(2 ^ 31 : Nat)) (2 ^ 31 : Nat) (by decide) == -1
