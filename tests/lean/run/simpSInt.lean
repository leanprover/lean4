#check_simp (-64 : Int8).toBitVec ~> 192#8
#check_simp (-64 : Int16).toBitVec ~> 65472#16
#check_simp (-64 : Int32).toBitVec ~> 4294967232#32
#check_simp (-64 : Int64).toBitVec ~> 18446744073709551552#64

-- see also simprocSInt.lean
