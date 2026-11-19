module

section

variable (x : Int)

#check_simp x = (-8 : Int8).toInt ~> x = -8
#check_simp x = (8 : Int8).toInt ~> x = 8
#check_simp x = (128 : Int8).toInt ~> x = -128
#check_simp x = (257 : Int8).toInt ~> x = 1
#check_simp x = (-8 : Int16).toInt ~> x = -8
#check_simp x = (8 : Int16).toInt ~> x = 8
#check_simp x = (32768 : Int16).toInt ~> x = -32768
#check_simp x = (65537 : Int16).toInt ~> x = 1
#check_simp x = (-8 : Int32).toInt ~> x = -8
#check_simp x = (8 : Int32).toInt ~> x = 8
#check_simp x = (2147483648 : Int32).toInt ~> x = -2147483648
#check_simp x = (4294967297 : Int32).toInt ~> x = 1
#check_simp x = (-8 : Int64).toInt ~> x = -8
#check_simp x = (8 : Int64).toInt ~> x = 8
#check_simp x = (9223372036854775808 : Int64).toInt ~> x = -9223372036854775808
#check_simp x = (18446744073709551617 : Int64).toInt ~> x = 1

end

section


end

section

variable (x : Int8)

example : (5 : Int8) = 5 := by decide
example : (5 : Int8) ≤ 5 := by decide
example : (5 : Int8) < 6 := by decide
example : Int8.toInt (-(-(-8))) + 8 = 0 := by simp +ground only
example : Int8.toInt (-8) + 8 = 0 := by simp +ground only
#check_simp (-5 : Int8).toNatClampNeg ~> 0
#check_simp (5 : Int8).toNatClampNeg ~> 5
#check_simp (-5 : Int8).toInt ~> -5
#check_simp (5 : Int8).toInt ~> 5
#check_simp x = - (-2) ~> x = 2
#check_simp x = -0 ~> x = 0
#check_simp x = - (-0) ~> x = 0
#check_simp x = - (-128) ~> x = 128
#check_simp x = - (-127) ~> x = 127
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = -3 + 2 ~> x = -1
#check_simp x = 2 * -3 ~> x = -6
#check_simp x = 2 - 3 ~> x = -1
#check_simp x = 2 - -3 ~> x = 5
#check_simp x = 4 / -3 ~> x = -1
#check_simp x = -5 % 3 ~> x = -2
#check_simp x = -4 &&& 7 ~> x = 4
#check_simp x = -4 ||| 3 ~> x = -1
#check_simp x = -4 ^^^ 5 ~> x = -7
#check_simp x = ~~~5 ~> x = -6
#check_simp x = ~~~(-1) ~> x = 0
#check_simp x = (-1 : Int8) <<< 3 ~> x = -8
#check_simp x = (64 : Int8) <<< 1 ~> x = -128
#check_simp x = (1 : Int8) <<< (-1) ~> x = -128
#check_simp x = (-8 : Int8) >>> 1 ~> x = -4
#check_simp x = (-128 : Int8) >>> 9 ~> x = -64
#check_simp x = (64 : Int8) >>> (-2) ~> x = 1
example : (-4 : Int8) &&& 7 = 4 ∧ (-4 : Int8) ||| 3 = -1 ∧ (-4 : Int8) ^^^ 5 = -7 ∧
    ~~~(5 : Int8) = -6 ∧ (1 : Int8) <<< (-1) = -128 ∧ (-128 : Int8) >>> 9 = -64 := by simp
#check_simp True = ((3 : Int8) < -3) ~> False
#check_simp True = ((3 : Int8) ≤ -2) ~> False
#check_simp True = ((-3 : Int8) > 3) ~> False
#check_simp True = ((-3 : Int8) ≥ 4) ~> False
#check_simp True = ((3 : Int8) = -3) ~> False
#check_simp True = ((-3 : Int8) ≠ -3) ~> False
#check_simp True = ((3 : Int8) == -3) ~> False
#check_simp True = ((-3 : Int8) != -3) ~> False
#check_simp x = Int8.ofIntLE 5 (by decide) (by decide) ~> x = 5
#check_simp x = Int8.ofIntLE (-5) (by decide) (by decide) ~> x = -5
#check_simp x = Int8.ofNat 5 ~> x = 5
#check_simp x = Int8.ofNat 257 ~> x = 1
#check_simp x = Int8.ofNat 128 ~> x = -128
#check_simp x = Int8.ofInt (-129) ~> x = 127
#check_simp x = Int8.ofInt (-5) ~> x = -5
#check_simp x = Int8.ofInt 5 ~> x = 5
#check_simp x = Int8.ofInt 257 ~> x = 1
#check_simp x = Int8.ofInt 128 ~> x = -128

end

section

variable (x : Int16)

example : (5 : Int16) = 5 := by decide
example : (5 : Int16) ≤ 5 := by decide
example : (5 : Int16) < 6 := by decide
example : Int16.toInt (-(-(-16))) + 16 = 0 := by simp +ground only
example : Int16.toInt (-16) + 16 = 0 := by simp +ground only
#check_simp (-5 : Int16).toNatClampNeg ~> 0
#check_simp (5 : Int16).toNatClampNeg ~> 5
#check_simp (-5 : Int16).toInt ~> -5
#check_simp (5 : Int16).toInt ~> 5
#check_simp x = - (-2) ~> x = 2
#check_simp x = -0 ~> x = 0
#check_simp x = - (-0) ~> x = 0
#check_simp x = - (-32768) ~> x = 32768
#check_simp x = - (-32767) ~> x = 32767
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = -3 + 2 ~> x = -1
#check_simp x = 2 * -3 ~> x = -6
#check_simp x = 2 - 3 ~> x = -1
#check_simp x = 2 - -3 ~> x = 5
#check_simp x = 4 / -3 ~> x = -1
#check_simp x = -5 % 3 ~> x = -2
#check_simp x = -4 &&& 7 ~> x = 4
#check_simp x = -4 ||| 3 ~> x = -1
#check_simp x = -4 ^^^ 5 ~> x = -7
#check_simp x = ~~~5 ~> x = -6
#check_simp x = ~~~(-1) ~> x = 0
#check_simp x = (-1 : Int16) <<< 3 ~> x = -8
#check_simp x = (16384 : Int16) <<< 1 ~> x = -32768
#check_simp x = (1 : Int16) <<< (-1) ~> x = -32768
#check_simp x = (-8 : Int16) >>> 1 ~> x = -4
#check_simp x = (-32768 : Int16) >>> 17 ~> x = -16384
#check_simp x = (16384 : Int16) >>> (-2) ~> x = 1
example : (-4 : Int16) &&& 7 = 4 ∧ (-4 : Int16) ||| 3 = -1 ∧ (-4 : Int16) ^^^ 5 = -7 ∧
    ~~~(5 : Int16) = -6 ∧ (1 : Int16) <<< (-1) = -32768 ∧ (-32768 : Int16) >>> 17 = -16384 := by simp
#check_simp True = ((3 : Int16) < -3) ~> False
#check_simp True = ((3 : Int16) ≤ -2) ~> False
#check_simp True = ((-3 : Int16) > 3) ~> False
#check_simp True = ((-3 : Int16) ≥ 4) ~> False
#check_simp True = ((3 : Int16) = -3) ~> False
#check_simp True = ((-3 : Int16) ≠ -3) ~> False
#check_simp True = ((3 : Int16) == -3) ~> False
#check_simp True = ((-3 : Int16) != -3) ~> False
#check_simp x = Int16.ofIntLE 5 (by decide) (by decide) ~> x = 5
#check_simp x = Int16.ofIntLE (-5) (by decide) (by decide) ~> x = -5
#check_simp x = Int16.ofNat 5 ~> x = 5
#check_simp x = Int16.ofNat 65537 ~> x = 1
#check_simp x = Int16.ofNat 32768 ~> x = -32768

end

section

variable (x : Int32)

example : (5 : Int32) = 5 := by decide
example : (5 : Int32) ≤ 5 := by decide
example : (5 : Int32) < 6 := by decide
example : Int32.toInt (-(-(-32))) + 32 = 0 := by simp +ground only
example : Int32.toInt (-32) + 32 = 0 := by simp +ground only
#check_simp (-5 : Int32).toNatClampNeg ~> 0
#check_simp (5 : Int32).toNatClampNeg ~> 5
#check_simp (-5 : Int32).toInt ~> -5
#check_simp (5 : Int32).toInt ~> 5
#check_simp x = - (-2) ~> x = 2
#check_simp x = -0 ~> x = 0
#check_simp x = - (-0) ~> x = 0
#check_simp x = - (-2147483648) ~> x = 2147483648
#check_simp x = - (-2147483647) ~> x = 2147483647
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = -3 + 2 ~> x = -1
#check_simp x = 2 * -3 ~> x = -6
#check_simp x = 2 - 3 ~> x = -1
#check_simp x = 2 - -3 ~> x = 5
#check_simp x = 4 / -3 ~> x = -1
#check_simp x = -5 % 3 ~> x = -2
#check_simp x = -4 &&& 7 ~> x = 4
#check_simp x = -4 ||| 3 ~> x = -1
#check_simp x = -4 ^^^ 5 ~> x = -7
#check_simp x = ~~~5 ~> x = -6
#check_simp x = ~~~(-1) ~> x = 0
#check_simp x = (-1 : Int32) <<< 3 ~> x = -8
#check_simp x = (1073741824 : Int32) <<< 1 ~> x = -2147483648
#check_simp x = (1 : Int32) <<< (-1) ~> x = -2147483648
#check_simp x = (-8 : Int32) >>> 1 ~> x = -4
#check_simp x = (-2147483648 : Int32) >>> 33 ~> x = -1073741824
#check_simp x = (1073741824 : Int32) >>> (-2) ~> x = 1
example : (-4 : Int32) &&& 7 = 4 ∧ (-4 : Int32) ||| 3 = -1 ∧ (-4 : Int32) ^^^ 5 = -7 ∧
    ~~~(5 : Int32) = -6 ∧ (1 : Int32) <<< (-1) = -2147483648 ∧ (-2147483648 : Int32) >>> 33 = -1073741824 := by simp
#check_simp True = ((3 : Int32) < -3) ~> False
#check_simp True = ((3 : Int32) ≤ -2) ~> False
#check_simp True = ((-3 : Int32) > 3) ~> False
#check_simp True = ((-3 : Int32) ≥ 4) ~> False
#check_simp True = ((3 : Int32) = -3) ~> False
#check_simp True = ((-3 : Int32) ≠ -3) ~> False
#check_simp True = ((3 : Int32) == -3) ~> False
#check_simp True = ((-3 : Int32) != -3) ~> False
#check_simp x = Int32.ofIntLE 5 (by decide) (by decide) ~> x = 5
#check_simp x = Int32.ofIntLE (-5) (by decide) (by decide) ~> x = -5
#check_simp x = Int32.ofNat 5 ~> x = 5
#check_simp x = Int32.ofNat 4294967297 ~> x = 1
#check_simp x = Int32.ofNat 2147483648 ~> x = -2147483648

end

section

variable (x : Int64)

example : (5 : Int64) = 5 := by decide
example : (5 : Int64) ≤ 5 := by decide
example : (5 : Int64) < 6 := by decide
example : Int64.toInt (-(-(-64))) + 64 = 0 := by simp +ground only
example : Int64.toInt (-64) + 64 = 0 := by simp +ground only
#check_simp (-5 : Int64).toNatClampNeg ~> 0
#check_simp (5 : Int64).toNatClampNeg ~> 5
#check_simp (-5 : Int64).toInt ~> -5
#check_simp (5 : Int64).toInt ~> 5
#check_simp x = - (-2) ~> x = 2
#check_simp x = -0 ~> x = 0
#check_simp x = - (-0) ~> x = 0
#check_simp x = - (-9223372036854775808) ~> x = 9223372036854775808
#check_simp x = - (-9223372036854775807) ~> x = 9223372036854775807
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = -3 + 2 ~> x = -1
#check_simp x = 2 * -3 ~> x = -6
#check_simp x = 2 - 3 ~> x = -1
#check_simp x = 2 - -3 ~> x = 5
#check_simp x = 4 / -3 ~> x = -1
#check_simp x = -5 % 3 ~> x = -2
#check_simp x = -4 &&& 7 ~> x = 4
#check_simp x = -4 ||| 3 ~> x = -1
#check_simp x = -4 ^^^ 5 ~> x = -7
#check_simp x = ~~~5 ~> x = -6
#check_simp x = ~~~(-1) ~> x = 0
#check_simp x = (-1 : Int64) <<< 3 ~> x = -8
#check_simp x = (4611686018427387904 : Int64) <<< 1 ~> x = -9223372036854775808
#check_simp x = (1 : Int64) <<< (-1) ~> x = -9223372036854775808
#check_simp x = (-8 : Int64) >>> 1 ~> x = -4
#check_simp x = (-9223372036854775808 : Int64) >>> 65 ~> x = -4611686018427387904
#check_simp x = (4611686018427387904 : Int64) >>> (-2) ~> x = 1
example : (-4 : Int64) &&& 7 = 4 ∧ (-4 : Int64) ||| 3 = -1 ∧ (-4 : Int64) ^^^ 5 = -7 ∧
    ~~~(5 : Int64) = -6 ∧ (1 : Int64) <<< (-1) = -9223372036854775808 ∧ (-9223372036854775808 : Int64) >>> 65 = -4611686018427387904 := by simp
#check_simp True = ((3 : Int32) < -3) ~> False
#check_simp True = ((3 : Int32) ≤ -2) ~> False
#check_simp True = ((-3 : Int32) > 3) ~> False
#check_simp True = ((-3 : Int32) ≥ 4) ~> False
#check_simp True = ((3 : Int32) = -3) ~> False
#check_simp True = ((-3 : Int32) ≠ -3) ~> False
#check_simp True = ((3 : Int32) == -3) ~> False
#check_simp True = ((-3 : Int32) != -3) ~> False
#check_simp x = Int64.ofIntLE 5 (by decide) (by decide) ~> x = 5
#check_simp x = Int64.ofIntLE (-5) (by decide) (by decide) ~> x = -5
#check_simp x = Int64.ofNat 5 ~> x = 5
#check_simp x = Int64.ofNat 18446744073709551617 ~> x = 1
#check_simp x = Int64.ofNat 9223372036854775808 ~> x = -9223372036854775808

end

section

#check_simp ISize.toNatClampNeg 2147483648 !~>
#check_simp ISize.toNatClampNeg 2147483647 ~> 2147483647
#check_simp ISize.toNatClampNeg (-1) ~> 0
#check_simp ISize.toNatClampNeg 0 ~> 0
#check_simp ISize.toNatClampNeg 1 ~> 1
#check_simp ISize.toNatClampNeg (-2147483649) !~>
#check_simp ISize.toNatClampNeg (-2147483648) ~> 0

#check_simp ISize.toInt 2147483648 !~>
#check_simp ISize.toInt 2147483647 ~> 2147483647
#check_simp ISize.toInt (-1) ~> -1
#check_simp ISize.toInt 0 ~> 0
#check_simp ISize.toInt 1 ~> 1
#check_simp ISize.toInt (-2147483649) !~>
#check_simp ISize.toInt (-2147483648) ~> -2147483648

end

-- see also simpSInt.lean
