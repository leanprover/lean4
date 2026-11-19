module

#check_simp (-64 : Int8).toBitVec ~> 192#8
#check_simp (-64 : Int16).toBitVec ~> 65472#16
#check_simp (-64 : Int32).toBitVec ~> 4294967232#32
#check_simp (-64 : Int64).toBitVec ~> 18446744073709551552#64

#check_simp (64 : UInt8).toUInt16 ~> 64
#check_simp (64 : UInt8).toUInt32 ~> 64
#check_simp (64 : UInt8).toUInt64 ~> 64
#check_simp (64 : UInt8).toUSize ~> 64

#check_simp (64 : UInt16).toUInt8 ~> 64
#check_simp (64 : UInt16).toUInt32 ~> 64
#check_simp (64 : UInt16).toUInt64 ~> 64
#check_simp (64 : UInt16).toUSize ~> 64

#check_simp (64 : UInt32).toUInt8 ~> 64
#check_simp (64 : UInt32).toUInt16 ~> 64
#check_simp (64 : UInt32).toUInt64 ~> 64
#check_simp (64 : UInt32).toUSize ~> 64

#check_simp (64 : UInt64).toUInt8 ~> 64
#check_simp (64 : UInt64).toUInt16 ~> 64
#check_simp (64 : UInt64).toUInt32 ~> 64
#check_simp (64 : UInt64).toUSize ~> 64

#check_simp (64 : USize).toUInt8 ~> 64
#check_simp (64 : USize).toUInt16 ~> 64
#check_simp (64 : USize).toUInt32 ~> 64

#check_simp (-64 : Int8).toInt16 ~> -64
#check_simp (-64 : Int8).toInt32 ~> -64
#check_simp (-64 : Int8).toInt64 ~> -64
#check_simp (-64 : Int8).toISize ~> -64

#check_simp (-64 : Int16).toInt8 ~> -64
#check_simp (-64 : Int16).toInt32 ~> -64
#check_simp (-64 : Int16).toInt64 ~> -64
#check_simp (-64 : Int16).toISize ~> -64

#check_simp (-64 : Int32).toInt8 ~> -64
#check_simp (-64 : Int32).toInt16 ~> -64
#check_simp (-64 : Int32).toInt64 ~> -64
#check_simp (-64 : Int32).toISize ~> -64

#check_simp (-64 : Int64).toInt8 ~> -64
#check_simp (-64 : Int64).toInt16 ~> -64
#check_simp (-64 : Int64).toInt32 ~> -64
#check_simp (-64 : Int64).toISize ~> -64

#check_simp (-64 : ISize).toInt8 ~> -64
#check_simp (-64 : ISize).toInt16 ~> -64
#check_simp (-64 : ISize).toInt32 ~> -64

-- This could be fixed with some additional work
#check_simp (-64 : ISize).toInt64 !~>

#check_simp (-127 : Int8).toInt16 ~> -127
#check_simp (-128 : Int8).toInt16 !~>

-- All of these could probably made to reduce using an additional simproc
#check_simp (300 : UInt8) !~>
#check_simp (300 : Int8) !~>
#check_simp (-32767 : Int16).toInt8 ~> -32767
#check_simp (-32768 : Int16).toInt8 ~> -32768
#check_simp (-32769 : Int16).toInt8 ~> -32769

#check_simp (-32767 : Int16).toInt32 ~> -32767
#check_simp (-32768 : Int16).toInt32 !~>

#check_simp (-2147483647 : Int32).toInt64 ~> -2147483647
#check_simp (-2147483648 : Int32).toInt64 !~>

-- see also simprocSInt.lean
