Import tactic
Import int
Definition a : Nat := 10
(* Trivial indicates a "proof by evaluation" *)
Theorem T1 : a > 0 := (by trivial)
Theorem T2 : a - 5 > 3 := (by trivial)
(* The next one is commented because it fails *)
(* Theorem T3 : a > 11 := Trivial *)
