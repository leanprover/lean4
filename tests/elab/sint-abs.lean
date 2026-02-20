/-- info: [0, 1, 1, 100, 127, -128] -/
#guard_msgs in
#eval [0, 1, -1, -100, Int8.minValue + 1, Int8.minValue].map Int8.abs

/-- info: [0, 1, 1, 100, 32767, -32768] -/
#guard_msgs in
#eval [0, 1, -1, -100, Int16.minValue + 1, Int16.minValue].map Int16.abs

/-- info: [0, 1, 1, 100, 2147483647, -2147483648] -/
#guard_msgs in
#eval [0, 1, -1, -100, Int32.minValue + 1, Int32.minValue].map Int32.abs

/-- info: [0, 1, 1, 100, 9223372036854775807, -9223372036854775808] -/
#guard_msgs in
#eval [0, 1, -1, -100, Int64.minValue + 1, Int64.minValue].map Int64.abs

/-- info: [0, 1, 1, 100] -/
#guard_msgs in
#eval [0, 1, -1, -100].map ISize.abs

/-- info: true -/
#guard_msgs in
#eval (ISize.minValue + 1).abs.toNatClampNeg == (ISize.minValue + 1).toInt.natAbs

/-- info: true -/
#guard_msgs in
#eval ISize.minValue.abs == ISize.minValue

example : Int8.minValue.abs = Int8.minValue := rfl
example : Int16.minValue.abs = Int16.minValue := rfl
example : Int32.minValue.abs = Int32.minValue := rfl
example : Int64.minValue.abs = Int64.minValue := rfl
-- TODO: prove once the relevant theory is available
-- example : ISize.minValue.abs = ISize.minValue := rfl
