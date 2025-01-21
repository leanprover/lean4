variable (x : USize)

/- USize.toNat -/

#check_simp USize.toNat 4294967296 !~>
#check_simp USize.toNat 4294967295 ~> 4294967295
#check_simp USize.toNat (x &&& 1) ~> x.toNat % 2
