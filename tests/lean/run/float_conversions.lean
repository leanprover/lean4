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

-- Float32 -> IntX

-- UIntX -> Float

-- UIntX -> Float32

-- IntX -> Float

-- IntX -> Float32
