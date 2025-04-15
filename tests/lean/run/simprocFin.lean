variable (n : Nat) [NeZero n]

/- basic operations -/

#check_simp (3 : Fin 7).succ ~> (4 : Fin 8)
#check_simp (6 : Fin 7).succ ~> (7 : Fin 8)
#check_simp Fin.last 0 ~> (0 : Fin 1)
#check_simp Fin.last 6 ~> (6 : Fin 7)
#check_simp Fin.ofNat' 6 3 ~> (3 : Fin 6)
#check_simp Fin.ofNat' 6 37 ~> (1 : Fin 6)
#check_simp Fin.rev (0 : Fin 7) ~> (6 : Fin 7)
#check_simp Fin.rev (3 : Fin 7) ~> (3 : Fin 7)
#check_simp Fin.castSucc (0 : Fin 7) ~> (0 : Fin 8)
#check_simp Fin.castSucc (3 : Fin 7) ~> (3 : Fin 8)
#check_simp Fin.castAdd 3 (0 : Fin 7) ~> (0 : Fin 10)
#check_simp Fin.castAdd 3 (3 : Fin 7) ~> (3 : Fin 10)
#check_simp Fin.castLT (3 : Fin 10) (by decide : 3 < 5) ~> (3 : Fin 5)
#check_simp Fin.castLE (by decide : 5 ≤ 37) (3 : Fin 5) ~> (3 : Fin 37)
#check_simp Fin.pred (3 : Fin 7) (by decide) ~> (2 : Fin 6)

/- arithmetic operation tests -/

#check_simp (3 : Fin 7) + (1 : Fin 7) ~> 4
#check_simp (3 : Fin 7) + (5 : Fin 7) ~> 1
#check_simp (3 : Fin 7) * (1 : Fin 7) ~> 3
#check_simp (3 : Fin 7) * (3 : Fin 7) ~> 2
#check_simp (3 : Fin 7) - (1 : Fin 7) ~> 2
#check_simp (3 : Fin 7) - (5 : Fin 7) ~> 5
#check_simp (3 : Fin 7) / (1 : Fin 7) ~> 3
#check_simp (3 : Fin 7) / (5 : Fin 7) ~> 0
#check_simp (3 : Fin 7) % (0 : Fin 7) ~> 3
#check_simp (3 : Fin 7) % (1 : Fin 7) ~> 0
#check_simp (3 : Fin 7) % (5 : Fin 7) ~> 3

#check_simp (3 : Fin n) + (5 : Fin n) !~>
#check_simp (3 : Fin n) * (5 : Fin n) !~>
#check_simp (3 : Fin n) - (5 : Fin n) !~>
#check_simp (3 : Fin n) / (5 : Fin n) !~>
#check_simp (3 : Fin n) % (5 : Fin n) !~>

#check_simp Fin.addNat (3 : Fin 7) 3 ~> (6 : Fin 10)
#check_simp Fin.natAdd 3 (3 : Fin 7) ~> (6 : Fin 10)
#check_simp Fin.subNat 2 (3 : Fin 7) (by decide) ~> (1 : Fin 5)

/- bitwise operations -/

#check_simp (3 : Fin 7) &&& (1 : Fin 7) ~> 1
#check_simp (3 : Fin 7) ||| (1 : Fin 7) ~> 3
#check_simp (3 : Fin 7) ^^^ (1 : Fin 7) ~> 2
#check_simp (3 : Fin 7) <<< (1 : Fin 7) ~> 6
#check_simp (3 : Fin 7) >>> (1 : Fin 7) ~> 1

/- predicate tests -/

#check_simp (3 : Fin 7) < (1 : Fin 7) ~> False
#check_simp (3 : Fin 7) < (5 : Fin 7) ~> True
#check_simp (3 : Fin 7) ≤ (1 : Fin 7) ~> False
#check_simp (3 : Fin 7) ≤ (5 : Fin 7) ~> True
#check_simp (3 : Fin 7) > (1 : Fin 7) ~> True
#check_simp (3 : Fin 7) > (5 : Fin 7) ~> False
#check_simp (3 : Fin 7) ≥ (1 : Fin 7) ~> True
#check_simp (3 : Fin 7) ≥ (5 : Fin 7) ~> False
#check_simp (3 : Fin 7) = (1 : Fin 7) ~> False
#check_simp (3 : Fin 7) = (5 : Fin 7) ~> False
#check_simp (3 : Fin 7) = (3 : Fin 7) ~> True
#check_simp (3 : Fin 7) ≠ (1 : Fin 7) ~> True
#check_simp (3 : Fin 7) ≠ (3 : Fin 7) ~> False
#check_simp (3 : Fin 7) ≠ (5 : Fin 7) ~> True

#check_simp (3 : Fin 7) == (1 : Fin 7) ~> false
#check_simp (3 : Fin 7) == (3 : Fin 7) ~> true
#check_simp (3 : Fin 7) == (5 : Fin 7) ~> false
#check_simp (3 : Fin 7) != (1 : Fin 7) ~> true
#check_simp (3 : Fin 7) != (3 : Fin 7) ~> false
#check_simp (3 : Fin 7) != (5 : Fin 7) ~> true
