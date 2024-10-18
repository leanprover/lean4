#check Int8
#eval Int8.ofInt (-130) |>.toBitVec.toInt
#eval Int8.ofNat (130) |>.toBitVec.toNat
