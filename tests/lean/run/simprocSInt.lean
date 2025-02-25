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

variable (x : Int)

#check_simp x = - (-2) ~> x = 2
#check_simp x = -0 ~> x = 0

example : Int8.toInt (-(-(-8))) + 8 = 0 := by simp +ground only
example : Int8.toInt (-8) + 8 = 0 := by simp +ground only

end

section

variable (x : Int8)

#check_simp x = - (-2) ~> x = 2
#check_simp x = -0 ~> x = 0
#check_simp x = - (-0) ~> x = 0
#check_simp x = - (-128) ~> x = -128
#check_simp x = - (-127) ~> x = 127
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = -3 + 2 ~> x = -1
#check_simp x = 2 * -3 ~> x = -6
#check_simp x = 2 - 3 ~> x = -1
#check_simp x = 2 - -3 ~> x = 5
#check_simp x = 4 / -3 ~> x = -1
#check_simp x = -5 % 3 ~> x = -2
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

#check_simp x = - (-2) ~> x = 2
#check_simp x = -0 ~> x = 0
#check_simp x = - (-0) ~> x = 0
#check_simp x = - (-32768) ~> x = -32768
#check_simp x = - (-32767) ~> x = 32767
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = -3 + 2 ~> x = -1
#check_simp x = 2 * -3 ~> x = -6
#check_simp x = 2 - 3 ~> x = -1
#check_simp x = 2 - -3 ~> x = 5
#check_simp x = 4 / -3 ~> x = -1
#check_simp x = -5 % 3 ~> x = -2
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
