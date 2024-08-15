#check_simp #[1,2,3,4,5][2]  ~> 3
#check_simp #[1,2,3,4,5][2]? ~> some 3
#check_simp #[1,2,3,4,5][7]? ~> none
#check_simp #[][0]? ~> none
#check_simp #[1,2,3,4,5][2]! ~> 3
#check_simp #[1,2,3,4,5][7]! ~> (default : Nat)
#check_simp (#[] : Array Nat)[0]! ~> (default : Nat)
