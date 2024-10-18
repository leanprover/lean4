#check Int8
#eval Int8.ofInt (-130) |>.toInt
#eval Int8.ofInt (-20) |>.toInt
#eval Int8.ofInt (-130) |>.toNat
#eval Int8.ofNat (10) |>.toNat
#eval Int8.ofNat (10) |>.toInt
#eval Int8.ofNat (130) |>.toNat
#eval Int8.ofNat (130) |>.toInt
#eval (130 : Int8) |>.toInt

#eval Int8.ofInt (-130)
#eval Int8.ofInt (-20)
#eval Int8.ofInt (-130)
#eval Int8.ofNat 10
#eval Int8.ofNat 10
#eval Int8.ofNat 130
#eval Int8.ofNat 130
#eval (130 : Int8)
#eval (-130 : Int8)
#eval (-2 : Int8)
#eval (2 : Int8)
