/-!
# Signed integer division overflow test

On x86_64, INT_MIN / -1 and INT_MIN % -1 cause a SIGFPE (floating point exception)
because the result overflows the destination register. This test verifies the fix.

The expected behavior (per BitVec.sdiv semantics): return minValue (wrapped result) for div,
and 0 for mod.
-/

-- Test that signed division handles overflow correctly
-- INT_MIN / -1 should return INT_MIN (wrapped)

#guard (Int8.minValue / -1 : Int8) == Int8.minValue
#guard (Int16.minValue / -1 : Int16) == Int16.minValue
#guard (Int32.minValue / -1 : Int32) == Int32.minValue
#guard (Int64.minValue / -1 : Int64) == Int64.minValue

-- Test that signed mod handles overflow correctly
-- INT_MIN % -1 should return 0

#guard (Int8.minValue % -1 : Int8) == 0
#guard (Int16.minValue % -1 : Int16) == 0
#guard (Int32.minValue % -1 : Int32) == 0
#guard (Int64.minValue % -1 : Int64) == 0

-- Also test via #eval to exercise the C runtime
#eval (Int8.minValue / -1 : Int8)
#eval (Int16.minValue / -1 : Int16)
#eval (Int32.minValue / -1 : Int32)
#eval (Int64.minValue / -1 : Int64)

#eval (Int8.minValue % -1 : Int8)
#eval (Int16.minValue % -1 : Int16)
#eval (Int32.minValue % -1 : Int32)
#eval (Int64.minValue % -1 : Int64)
