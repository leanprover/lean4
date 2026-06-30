example : (-2147483649 : Int8).toInt16 = -1 := by native_decide
example : (-2147483649 : Int8).toInt16 = -1 := by rfl
example : (-2147483649 : Int8).toInt32 = -1 := by native_decide
example : (-2147483649 : Int8).toInt32 = -1 := by rfl
example : (-2147483649 : Int8).toInt64 = -1 := by native_decide
example : (-2147483649 : Int8).toInt64 = -1 := by rfl
example : (-2147483649 : Int8).toISize = -1 := by native_decide
-- TODO: add proof once the theory is available
-- example : (-2147483649 : Int8).toISize = -1 := by rfl

example : (-2147483649 : Int16).toInt8 = -1 := by native_decide
example : (-2147483649 : Int16).toInt8 = -1 := by rfl
example : (-2147483649 : Int16).toInt32 = -1 := by native_decide
example : (-2147483649 : Int16).toInt32 = -1 := by rfl
example : (-2147483649 : Int16).toInt64 = -1 := by native_decide
example : (-2147483649 : Int16).toInt64 = -1 := by rfl
example : (-2147483649 : Int16).toISize = -1 := by native_decide
-- TODO: add proof once the theory is available
-- example : (-2147483649 : Int16).toISize = -1 := by rfl

example : (-2147483649 : Int32).toInt8 = -1 := by native_decide
example : (-2147483649 : Int32).toInt8 = -1 := by rfl
example : (-2147483649 : Int32).toInt16 = -1 := by native_decide
example : (-2147483649 : Int32).toInt16 = -1 := by rfl
example : (-2147483649 : Int32).toInt64 = 2147483647 := by native_decide
example : (-2147483649 : Int32).toInt64 = 2147483647 := by rfl
example : (-2147483649 : Int32).toISize = 2147483647 := by native_decide
example : (-2147483649 : Int32).toISize = 2147483647 := by rfl

example : (-2147483649 : Int64).toInt8 = -1 := by native_decide
example : (-2147483649 : Int64).toInt8 = -1 := by rfl
example : (-2147483649 : Int64).toInt16 = -1 := by native_decide
example : (-2147483649 : Int64).toInt16 = -1 := by rfl
example : (-2147483649 : Int64).toInt32 = 2147483647 := by native_decide
example : (-2147483649 : Int64).toInt32 = 2147483647 := by rfl
example : (-2147483649 : Int64).toISize = 2147483647 ∨ (-2147483649 : Int64).toISize = -2147483649 := by native_decide
-- TODO: add proof once the theory is available
-- example : (-2147483649 : Int64).toISize = 2147483647 := by rfl

example : (-2147483649 : ISize).toInt8 = -1 := by native_decide
-- TODO: add proof once the theory is available
-- example : (-2147483649 : ISize).toInt8 = -1 := by rfl
example : (-2147483649 : ISize).toInt16 = -1 := by native_decide
-- TODO: add proof once the theory is available
-- example : (-2147483649 : ISize).toInt16 = -1 := by rfl
example : (-2147483649 : ISize).toInt32 = 2147483647 := by native_decide
-- TODO: add proof once the theory is available
-- example : (-2147483649 : ISize).toInt32 = 2147483647 := by rfl
example : (-2147483649 : ISize).toInt64 = 2147483647 ∨ (-2147483649 : ISize).toInt64 = -2147483649 := by native_decide
-- TODO: add proof once the theory is available
-- example : (-2147483649 : ISize).toInt64 = 2147483647 := by decide
