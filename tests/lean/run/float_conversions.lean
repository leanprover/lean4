def check (b : Bool) : IO Unit :=
  unless b do
    throw $ IO.userError "check failed"

-- Float -> UIntX

def testFloatToUIntX : IO Unit := do
  check <| (1/0 : Float).toUInt8 == 255
  check <| (0/0 : Float).toUInt8 == 0
  check <| (-1/0 : Float).toUInt8 == 0
  check <| (-600 : Float).toUInt8 == 0
  check <| (-200 : Float).toUInt8 == 0
  check <| (200 : Float).toUInt8 == 200
  check <| (255 : Float).toUInt8 == 255
  check <| (256 : Float).toUInt8 == 255
  check <| (600 : Float).toUInt8 == 255

  check <| (1/0 : Float).toUInt16 == 65535
  check <| (0/0 : Float).toUInt16 == 0
  check <| (-1/0 : Float).toUInt16 == 0
  check <| (-600000 : Float).toUInt16 == 0
  check <| (-60000 : Float).toUInt16 == 0
  check <| (60000 : Float).toUInt16 == 60000
  check <| (65535 : Float).toUInt16 == 65535
  check <| (65536 : Float).toUInt16 == 65535
  check <| (600000 : Float).toUInt16 == 65535

  check <| (1/0 : Float).toUInt32 == 4294967295
  check <| (0/0 : Float).toUInt32 == 0
  check <| (-1/0 : Float).toUInt32 == 0
  check <| (-4000000000 : Float).toUInt32 == 0
  check <| (-40000000000 : Float).toUInt32 == 0
  check <| (4000000000 : Float).toUInt32 == 4000000000
  check <| (4294967295 : Float).toUInt32 == 4294967295
  check <| (4294967296 : Float).toUInt32 == 4294967295
  check <| (40000000000 : Float).toUInt32 == 4294967295

  check <| (1/0 : Float).toUInt64 == 18446744073709551615
  check <| (0/0 : Float).toUInt64 == 0
  check <| (-1/0 : Float).toUInt64 == 0
  check <| (-4000000000 : Float).toUInt64 == 0
  check <| (-40000000000 : Float).toUInt64 == 0
  check <| (10000000000000000000 : Float).toUInt64 == 10000000000000000000
  check <| (18446744073709551615 : Float).toUInt64 == 18446744073709551615
  check <| (18446744073709551616 : Float).toUInt64 == 18446744073709551615
  check <| (100000000000000000000 : Float).toUInt64 == 18446744073709551615

  check <| (1/0 : Float).toUSize == 4294967295 || (1/0 : Float).toUSize == 18446744073709551615
  check <| (0/0 : Float).toUSize == 0
  check <| (-1/0 : Float).toUSize == 0
  check <| (-4000000000 : Float).toUSize == 0
  check <| (-40000000000 : Float).toUSize == 0
  check <| (4000000000 : Float).toUSize == 4000000000
  check <| (4294967295 : Float).toUSize == 4294967295
  check <| (4294967296 : Float).toUSize == 4294967295 || (4294967296 : Float).toUSize == 4294967296
  check <| (40000000000 : Float).toUSize == 4294967295 || (40000000000 : Float).toUSize == 40000000000
  return ()

#guard_msgs in
#eval testFloatToUIntX

-- Float32 -> UIntX

def testFloat32ToUIntX : IO Unit := do
  check <| (1/0 : Float32).toUInt8 == 255
  check <| (0/0 : Float32).toUInt8 == 0
  check <| (-1/0 : Float32).toUInt8 == 0
  check <| (-600 : Float32).toUInt8 == 0
  check <| (-200 : Float32).toUInt8 == 0
  check <| (200 : Float32).toUInt8 == 200
  check <| (255 : Float32).toUInt8 == 255
  check <| (256 : Float32).toUInt8 == 255
  check <| (600 : Float32).toUInt8 == 255

  check <| (1/0 : Float32).toUInt16 == 65535
  check <| (0/0 : Float32).toUInt16 == 0
  check <| (-1/0 : Float32).toUInt16 == 0
  check <| (-600000 : Float32).toUInt16 == 0
  check <| (-60000 : Float32).toUInt16 == 0
  check <| (60000 : Float32).toUInt16 == 60000
  check <| (65535 : Float32).toUInt16 == 65535
  check <| (65536 : Float32).toUInt16 == 65535
  check <| (600000 : Float32).toUInt16 == 65535

  check <| (1/0 : Float32).toUInt32 == 4294967295
  check <| (0/0 : Float32).toUInt32 == 0
  check <| (-1/0 : Float32).toUInt32 == 0
  check <| (-4000000000 : Float32).toUInt32 == 0
  check <| (-40000000000 : Float32).toUInt32 == 0
  check <| (4000000000 : Float32).toUInt32 == 4000000000
  check <| (4294967295 : Float32).toUInt32 == 4294967295
  check <| (4294967296 : Float32).toUInt32 == 4294967295
  check <| (40000000000 : Float32).toUInt32 == 4294967295

  check <| (1/0 : Float32).toUInt64 == 18446744073709551615
  check <| (0/0 : Float32).toUInt64 == 0
  check <| (-1/0 : Float32).toUInt64 == 0
  check <| (-4000000000 : Float32).toUInt64 == 0
  check <| (-40000000000 : Float32).toUInt64 == 0
  check <| (10000000000000000000 : Float32).toUInt64 == 9999999980506447872 -- imprecision
  check <| (18446744073709551615 : Float32).toUInt64 == 18446744073709551615
  check <| (18446744073709551616 : Float32).toUInt64 == 18446744073709551615
  check <| (100000000000000000000 : Float32).toUInt64 == 18446744073709551615

  check <| (1/0 : Float32).toUSize == 4294967295 || (1/0 : Float32).toUSize == 18446744073709551615
  check <| (0/0 : Float32).toUSize == 0
  check <| (-1/0 : Float32).toUSize == 0
  check <| (-4000000000 : Float32).toUSize == 0
  check <| (-40000000000 : Float32).toUSize == 0
  check <| (4000000000 : Float32).toUSize == 4000000000
  check <| (4294967295 : Float32).toUSize == 4294967295 || (4294967295 : Float32).toUSize == 4294967296 -- imprecision
  check <| (4294967296 : Float32).toUSize == 4294967295 || (4294967296 : Float32).toUSize == 4294967296
  check <| (40000000000 : Float32).toUSize == 4294967295 || (40000000000 : Float32).toUSize == 40000000000
  return ()

#guard_msgs in
#eval testFloat32ToUIntX

-- Float -> IntX

def testFloatToIntX : IO Unit := do
  check <| (1/0 : Float).toInt8 == 127
  check <| (0/0 : Float).toInt8 == 0
  check <| (-1/0 : Float).toInt8 == -128
  check <| (-600 : Float).toInt8 == -128
  check <| (-129 : Float).toInt8 == -128
  check <| (-128 : Float).toInt8 == -128
  check <| (-127 : Float).toInt8 == -127
  check <| (-100 : Float).toInt8 == -100
  check <| (100 : Float).toInt8 == 100
  check <| (127 : Float).toInt8 == 127
  check <| (128 : Float).toInt8 == 127
  check <| (600 : Float).toInt8 == 127

  check <| (1/0 : Float).toInt16 == 32767
  check <| (0/0 : Float).toInt16 == 0
  check <| (-1/0 : Float).toInt16 == -32768
  check <| (-600000 : Float).toInt16 == -32768
  check <| (-32769 : Float).toInt16 == -32768
  check <| (-32768 : Float).toInt16 == -32768
  check <| (-32767 : Float).toInt16 == -32767
  check <| (30000 : Float).toInt16 == 30000
  check <| (32767 : Float).toInt16 == 32767
  check <| (32768 : Float).toInt16 == 32767
  check <| (600000 : Float).toInt16 == 32767

  check <| (1/0 : Float).toInt32 == 2147483647
  check <| (0/0 : Float).toInt32 == 0
  check <| (-1/0 : Float).toInt32 == -2147483648
  check <| (-40000000000 : Float).toInt32 == -2147483648
  check <| (-2147483649 : Float).toInt32 == -2147483648
  check <| (-2147483648 : Float).toInt32 == -2147483648
  check <| (-2147483647 : Float).toInt32 == -2147483647
  check <| (-2000000000 : Float).toInt32 == -2000000000
  check <| (2000000000 : Float).toInt32 == 2000000000
  check <| (2147483647 : Float).toInt32 == 2147483647
  check <| (2147483648 : Float).toInt32 == 2147483647
  check <| (40000000000 : Float).toInt32 == 2147483647

  check <| (1/0 : Float).toInt64 == 9223372036854775807
  check <| (0/0 : Float).toInt64 == 0
  check <| (-1/0 : Float).toInt64 == -9223372036854775808
  check <| (-10000000000000000000 : Float).toInt64 == -9223372036854775808
  check <| (-9223372036854775808 : Float).toInt64 == -9223372036854775808
  check <| (-2000000000 : Float).toInt64 == -2000000000
  check <| (2000000000 : Float).toInt64 == 2000000000
  check <| (9223372036854775808 : Float).toInt64 == 9223372036854775807
  check <| (10000000000000000000 : Float).toInt64 == 9223372036854775807

  check <| (1/0 : Float).toISize == 2147483647 || (1/0 : Float).toISize == 9223372036854775807
  check <| (0/0 : Float).toISize == 0
  check <| (-1/0 : Float).toISize == -2147483648 || (-1/0 : Float).toISize = -9223372036854775808
  check <| (-2000000000 : Float).toISize == -2000000000
  check <| (4000000000 : Float).toISize == 4000000000
  check <| (2147483647 : Float).toISize == 2147483647
  check <| (2147483648 : Float).toISize == 2147483647 || (2147483648 : Float).toISize == 2147483648
  check <| (20000000000 : Float).toISize == 2147483647 || (20000000000 : Float).toISize == 20000000000
  return ()

#guard_msgs in
#eval testFloatToIntX

-- Float32 -> IntX

def testFloat32ToIntX : IO Unit := do
  check <| (1/0 : Float32).toInt8 == 127
  check <| (0/0 : Float32).toInt8 == 0
  check <| (-1/0 : Float32).toInt8 == -128
  check <| (-600 : Float32).toInt8 == -128
  check <| (-129 : Float32).toInt8 == -128
  check <| (-128 : Float32).toInt8 == -128
  check <| (-127 : Float32).toInt8 == -127
  check <| (-100 : Float32).toInt8 == -100
  check <| (100 : Float32).toInt8 == 100
  check <| (127 : Float32).toInt8 == 127
  check <| (128 : Float32).toInt8 == 127
  check <| (600 : Float32).toInt8 == 127

  check <| (1/0 : Float32).toInt16 == 32767
  check <| (0/0 : Float32).toInt16 == 0
  check <| (-1/0 : Float32).toInt16 == -32768
  check <| (-600000 : Float32).toInt16 == -32768
  check <| (-32769 : Float32).toInt16 == -32768
  check <| (-32768 : Float32).toInt16 == -32768
  check <| (-32767 : Float32).toInt16 == -32767
  check <| (30000 : Float32).toInt16 == 30000
  check <| (32767 : Float32).toInt16 == 32767
  check <| (32768 : Float32).toInt16 == 32767
  check <| (600000 : Float32).toInt16 == 32767

  check <| (1/0 : Float32).toInt32 == 2147483647
  check <| (0/0 : Float32).toInt32 == 0
  check <| (-1/0 : Float32).toInt32 == -2147483648
  check <| (-40000000000 : Float32).toInt32 == -2147483648
  check <| (-2147483649 : Float32).toInt32 == -2147483648
  check <| (-2147483648 : Float32).toInt32 == -2147483648
  check <| (-2147483647 : Float32).toInt32 == -2147483648 -- imprecision
  check <| (-2000000000 : Float32).toInt32 == -2000000000
  check <| (2000000000 : Float32).toInt32 == 2000000000
  check <| (2147483647 : Float32).toInt32 == 2147483647
  check <| (2147483648 : Float32).toInt32 == 2147483647
  check <| (40000000000 : Float32).toInt32 == 2147483647

  check <| (1/0 : Float32).toInt64 == 9223372036854775807
  check <| (0/0 : Float32).toInt64 == 0
  check <| (-1/0 : Float32).toInt64 == -9223372036854775808
  check <| (-10000000000000000000 : Float32).toInt64 == -9223372036854775808
  check <| (-9223372036854775808 : Float32).toInt64 == -9223372036854775808
  check <| (-2000000000 : Float32).toInt64 == -2000000000
  check <| (2000000000 : Float32).toInt64 == 2000000000
  check <| (9223372036854775808 : Float32).toInt64 == 9223372036854775807
  check <| (10000000000000000000 : Float32).toInt64 == 9223372036854775807

  check <| (1/0 : Float32).toISize == 2147483647 || (1/0 : Float32).toISize == 9223372036854775807
  check <| (0/0 : Float32).toISize == 0
  check <| (-1/0 : Float32).toISize == -2147483648 || (-1/0 : Float32).toISize = -9223372036854775808
  check <| (-2000000000 : Float32).toISize == -2000000000
  check <| (4000000000 : Float32).toISize == 4000000000
  check <| (2147483647 : Float32).toISize == 2147483648 -- imprecision
  check <| (2147483648 : Float32).toISize == 2147483647 || (2147483648 : Float32).toISize == 2147483648
  check <| (20000000000 : Float32).toISize == 2147483647 || (20000000000 : Float32).toISize == 20000000000
  return ()

#guard_msgs in
#eval testFloat32ToIntX

-- UIntX -> Float

def testUIntXToFloat : IO Unit := do
  check <| (0 : UInt8).toFloat == 0
  check <| (1 : UInt8).toFloat == 1
  check <| (254 : UInt8).toFloat == 254
  check <| (255 : UInt8).toFloat == 255

  check <| (0 : UInt16).toFloat == 0
  check <| (1 : UInt16).toFloat == 1
  check <| (65534 : UInt16).toFloat == 65534
  check <| (65535 : UInt16).toFloat == 65535

  check <| (0 : UInt32).toFloat == 0
  check <| (1 : UInt32).toFloat == 1
  check <| (4294967294 : UInt32).toFloat == 4294967294
  check <| (4294967295 : UInt32).toFloat == 4294967295

  check <| (0 : UInt64).toFloat == 0
  check <| (1 : UInt64).toFloat == 1
  check <| (18446744073709551614 : UInt64).toFloat == 18446744073709551614
  check <| (18446744073709551615 : UInt64).toFloat == 18446744073709551615

  check <| (0 : USize).toFloat == 0
  check <| (1 : USize).toFloat == 1
  check <| (4294967294 : USize).toFloat == 4294967294
  check <| (4294967295 : USize).toFloat == 4294967295
  return ()

#guard_msgs in
#eval testUIntXToFloat

-- UIntX -> Float32

def testUIntXToFloat32 : IO Unit := do
  check <| (0 : UInt8).toFloat32 == 0
  check <| (1 : UInt8).toFloat32 == 1
  check <| (254 : UInt8).toFloat32 == 254
  check <| (255 : UInt8).toFloat32 == 255

  check <| (0 : UInt16).toFloat32 == 0
  check <| (1 : UInt16).toFloat32 == 1
  check <| (65534 : UInt16).toFloat32 == 65534
  check <| (65535 : UInt16).toFloat32 == 65535

  check <| (0 : UInt32).toFloat32 == 0
  check <| (1 : UInt32).toFloat32 == 1
  check <| (4294967294 : UInt32).toFloat32 == 4294967294
  check <| (4294967295 : UInt32).toFloat32 == 4294967295

  check <| (0 : UInt64).toFloat32 == 0
  check <| (1 : UInt64).toFloat32 == 1
  check <| (18446744073709551614 : UInt64).toFloat32 == 18446744073709551614
  check <| (18446744073709551615 : UInt64).toFloat32 == 18446744073709551615

  check <| (0 : USize).toFloat32 == 0
  check <| (1 : USize).toFloat32 == 1
  check <| (4294967294 : USize).toFloat32 == 4294967294
  check <| (4294967295 : USize).toFloat32 == 4294967295
  return ()

#guard_msgs in
#eval testUIntXToFloat32

-- IntX -> Float

def testIntXToFloat : IO Unit := do
  check <| (-128 : Int8).toFloat == -128
  check <| (-127 : Int8).toFloat == -127
  check <| (-1 : Int8).toFloat == -1
  check <| (0 : Int8).toFloat == 0
  check <| (1 : Int8).toFloat == 1
  check <| (126 : Int8).toFloat == 126
  check <| (127 : Int8).toFloat == 127

  check <| (-32768 : Int16).toFloat == -32768
  check <| (-32767 : Int16).toFloat == -32767
  check <| (-1 : Int16).toFloat == -1
  check <| (0 : Int16).toFloat == 0
  check <| (1 : Int16).toFloat == 1
  check <| (32766 : Int16).toFloat == 32766
  check <| (32767 : Int16).toFloat == 32767

  check <| (-2147483648 : Int32).toFloat == -2147483648
  check <| (-2147483647 : Int32).toFloat == -2147483647
  check <| (-1 : Int32).toFloat == -1
  check <| (0 : Int32).toFloat == 0
  check <| (1 : Int32).toFloat == 1
  check <| (2147483646 : Int32).toFloat == 2147483646
  check <| (2147483647 : Int32).toFloat == 2147483647

  check <| (-9223372036854775808 : Int64).toFloat == -9223372036854775808
  check <| (-9223372036854775807 : Int64).toFloat == -9223372036854775807
  check <| (-1 : Int64).toFloat == -1
  check <| (0 : Int64).toFloat == 0
  check <| (1 : Int64).toFloat == 1
  check <| (9223372036854775806 : Int64).toFloat == 9223372036854775806
  check <| (9223372036854775807 : Int64).toFloat == 9223372036854775807

  check <| (-2147483648 : ISize).toFloat == -2147483648
  check <| (-2147483647 : ISize).toFloat == -2147483647
  check <| (-1 : ISize).toFloat == -1
  check <| (0 : ISize).toFloat == 0
  check <| (1 : ISize).toFloat == 1
  check <| (2147483646 : ISize).toFloat == 2147483646
  check <| (2147483647 : ISize).toFloat == 2147483647
  return ()

#guard_msgs in
#eval testIntXToFloat

-- IntX -> Float32

def testIntXToFloat32 : IO Unit := do
  check <| (-128 : Int8).toFloat32 == -128
  check <| (-127 : Int8).toFloat32 == -127
  check <| (-1 : Int8).toFloat32 == -1
  check <| (0 : Int8).toFloat32 == 0
  check <| (1 : Int8).toFloat32 == 1
  check <| (126 : Int8).toFloat32 == 126
  check <| (127 : Int8).toFloat32 == 127

  check <| (-32768 : Int16).toFloat32 == -32768
  check <| (-32767 : Int16).toFloat32 == -32767
  check <| (-1 : Int16).toFloat32 == -1
  check <| (0 : Int16).toFloat32 == 0
  check <| (1 : Int16).toFloat32 == 1
  check <| (32766 : Int16).toFloat32 == 32766
  check <| (32767 : Int16).toFloat32 == 32767

  check <| (-2147483648 : Int32).toFloat32 == -2147483648
  check <| (-2147483647 : Int32).toFloat32 == -2147483647
  check <| (-1 : Int32).toFloat32 == -1
  check <| (0 : Int32).toFloat32 == 0
  check <| (1 : Int32).toFloat32 == 1
  check <| (2147483646 : Int32).toFloat32 == 2147483646
  check <| (2147483647 : Int32).toFloat32 == 2147483647

  check <| (-9223372036854775808 : Int64).toFloat32 == -9223372036854775808
  check <| (-9223372036854775807 : Int64).toFloat32 == -9223372036854775807
  check <| (-1 : Int64).toFloat32 == -1
  check <| (0 : Int64).toFloat32 == 0
  check <| (1 : Int64).toFloat32 == 1
  check <| (9223372036854775806 : Int64).toFloat32 == 9223372036854775806
  check <| (9223372036854775807 : Int64).toFloat32 == 9223372036854775807

  check <| (-2147483648 : ISize).toFloat32 == -2147483648
  check <| (-2147483647 : ISize).toFloat32 == -2147483647
  check <| (-1 : ISize).toFloat32 == -1
  check <| (0 : ISize).toFloat32 == 0
  check <| (1 : ISize).toFloat32 == 1
  check <| (2147483646 : ISize).toFloat32 == 2147483646
  check <| (2147483647 : ISize).toFloat32 == 2147483647
  return ()

#guard_msgs in
#eval testIntXToFloat32
