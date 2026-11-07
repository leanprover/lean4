module

section

variable (x : Nat)

#check_simp x = (8 : UInt8).toNat ~> x = 8
#check_simp x = (257 : UInt8).toNat ~> x = 1
#check_simp x = (8 : UInt16).toNat ~> x = 8
#check_simp x = (65537 : UInt16).toNat ~> x = 1
#check_simp x = (8 : UInt32).toNat ~> x = 8
#check_simp x = (4294967297 : UInt32).toNat ~> x = 1
#check_simp x = (8 : UInt64).toNat ~> x = 8
#check_simp x = (18446744073709551617 : UInt64).toNat ~> x = 1

end

section

variable (x : UInt8)

example : (5 : UInt8) = 5 := by decide
example : (5 : UInt8) ≤ 5 := by decide
example : (5 : UInt8) < 6 := by decide
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = 2 * 3 ~> x = 6
#check_simp x = 2 - 3 ~> x = 255
#check_simp x = 4 / 3 ~> x = 1
#check_simp x = 5 % 3 ~> x = 2
#check_simp x = 12 &&& 10 ~> x = 8
#check_simp x = 12 ||| 10 ~> x = 14
#check_simp x = 12 ^^^ 10 ~> x = 6
#check_simp x = ~~~5 ~> x = 250
#check_simp x = (3 : UInt8) <<< 2 ~> x = 12
#check_simp x = (128 : UInt8) <<< 1 ~> x = 0
#check_simp x = (1 : UInt8) <<< 9 ~> x = 2
#check_simp x = (12 : UInt8) >>> 2 ~> x = 3
#check_simp x = (12 : UInt8) >>> 10 ~> x = 3
example : (12 : UInt8) &&& 10 = 8 ∧ (12 : UInt8) ||| 10 = 14 ∧ (12 : UInt8) ^^^ 10 = 6 ∧
    ~~~(5 : UInt8) = 250 ∧ (1 : UInt8) <<< 9 = 2 ∧ (12 : UInt8) >>> 10 = 3 := by simp
#check_simp True = ((3 : UInt8) < 3) ~> False
#check_simp True = ((3 : UInt8) ≤ 2) ~> False
#check_simp True = ((3 : UInt8) > 3) ~> False
#check_simp True = ((3 : UInt8) ≥ 4) ~> False
#check_simp True = ((3 : UInt8) = 4) ~> False
#check_simp True = ((3 : UInt8) ≠ 3) ~> False
#check_simp True = ((3 : UInt8) == 4) ~> False
#check_simp True = ((3 : UInt8) != 3) ~> False
#check_simp x = UInt8.ofNatLT 5 (by decide) ~> x = 5
#check_simp x = UInt8.ofNat 5 ~> x = 5
#check_simp x = UInt8.ofNat 257 ~> x = 1

end

section

variable (x : UInt16)

example : (5 : UInt16) = 5 := by decide
example : (5 : UInt16) ≤ 5 := by decide
example : (5 : UInt16) < 6 := by decide
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = 2 * 3 ~> x = 6
#check_simp x = 2 - 3 ~> x = 65535
#check_simp x = 4 / 3 ~> x = 1
#check_simp x = 5 % 3 ~> x = 2
#check_simp x = 12 &&& 10 ~> x = 8
#check_simp x = 12 ||| 10 ~> x = 14
#check_simp x = 12 ^^^ 10 ~> x = 6
#check_simp x = ~~~5 ~> x = 65530
#check_simp x = (3 : UInt16) <<< 2 ~> x = 12
#check_simp x = (32768 : UInt16) <<< 1 ~> x = 0
#check_simp x = (1 : UInt16) <<< 17 ~> x = 2
#check_simp x = (12 : UInt16) >>> 2 ~> x = 3
#check_simp x = (12 : UInt16) >>> 18 ~> x = 3
example : (12 : UInt16) &&& 10 = 8 ∧ (12 : UInt16) ||| 10 = 14 ∧ (12 : UInt16) ^^^ 10 = 6 ∧
    ~~~(5 : UInt16) = 65530 ∧ (1 : UInt16) <<< 17 = 2 ∧ (12 : UInt16) >>> 18 = 3 := by simp
#check_simp True = ((3 : UInt16) < 3) ~> False
#check_simp True = ((3 : UInt16) ≤ 2) ~> False
#check_simp True = ((3 : UInt16) > 3) ~> False
#check_simp True = ((3 : UInt16) ≥ 4) ~> False
#check_simp True = ((3 : UInt16) = 4) ~> False
#check_simp True = ((3 : UInt16) ≠ 3) ~> False
#check_simp True = ((3 : UInt16) == 4) ~> False
#check_simp True = ((3 : UInt16) != 3) ~> False
#check_simp x = UInt16.ofNatLT 5 (by decide) ~> x = 5
#check_simp x = UInt16.ofNat 5 ~> x = 5
#check_simp x = UInt16.ofNat 65537 ~> x = 1

end

section

variable (x : UInt32)

example : (5 : UInt32) = 5 := by decide
example : (5 : UInt32) ≤ 5 := by decide
example : (5 : UInt32) < 6 := by decide
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = 2 * 3 ~> x = 6
#check_simp x = 2 - 3 ~> x = 4294967295
#check_simp x = 4 / 3 ~> x = 1
#check_simp x = 5 % 3 ~> x = 2
#check_simp x = 12 &&& 10 ~> x = 8
#check_simp x = 12 ||| 10 ~> x = 14
#check_simp x = 12 ^^^ 10 ~> x = 6
#check_simp x = ~~~5 ~> x = 4294967290
#check_simp x = (3 : UInt32) <<< 2 ~> x = 12
#check_simp x = (2147483648 : UInt32) <<< 1 ~> x = 0
#check_simp x = (1 : UInt32) <<< 33 ~> x = 2
#check_simp x = (12 : UInt32) >>> 2 ~> x = 3
#check_simp x = (12 : UInt32) >>> 34 ~> x = 3
example : (12 : UInt32) &&& 10 = 8 ∧ (12 : UInt32) ||| 10 = 14 ∧ (12 : UInt32) ^^^ 10 = 6 ∧
    ~~~(5 : UInt32) = 4294967290 ∧ (1 : UInt32) <<< 33 = 2 ∧ (12 : UInt32) >>> 34 = 3 := by simp
#check_simp True = ((3 : UInt32) < 3) ~> False
#check_simp True = ((3 : UInt32) ≤ 2) ~> False
#check_simp True = ((3 : UInt32) > 3) ~> False
#check_simp True = ((3 : UInt32) ≥ 4) ~> False
#check_simp True = ((3 : UInt32) = 4) ~> False
#check_simp True = ((3 : UInt32) ≠ 3) ~> False
#check_simp True = ((3 : UInt32) == 4) ~> False
#check_simp True = ((3 : UInt32) != 3) ~> False
#check_simp x = UInt32.ofNatLT 5 (by decide) ~> x = 5
#check_simp x = UInt32.ofNat 5 ~> x = 5
#check_simp x = UInt32.ofNat 4294967297 ~> x = 1

end

section

variable (x : UInt64)

example : (5 : UInt64) = 5 := by decide
example : (5 : UInt64) ≤ 5 := by decide
example : (5 : UInt64) < 6 := by decide
#check_simp x = 2 + 3 ~> x = 5
#check_simp x = 2 * 3 ~> x = 6
#check_simp x = 2 - 3 ~> x = 18446744073709551615
#check_simp x = 4 / 3 ~> x = 1
#check_simp x = 5 % 3 ~> x = 2
#check_simp x = 12 &&& 10 ~> x = 8
#check_simp x = 12 ||| 10 ~> x = 14
#check_simp x = 12 ^^^ 10 ~> x = 6
#check_simp x = ~~~5 ~> x = 18446744073709551610
#check_simp x = (3 : UInt64) <<< 2 ~> x = 12
#check_simp x = (9223372036854775808 : UInt64) <<< 1 ~> x = 0
#check_simp x = (1 : UInt64) <<< 65 ~> x = 2
#check_simp x = (12 : UInt64) >>> 2 ~> x = 3
#check_simp x = (12 : UInt64) >>> 66 ~> x = 3
example : (12 : UInt64) &&& 10 = 8 ∧ (12 : UInt64) ||| 10 = 14 ∧ (12 : UInt64) ^^^ 10 = 6 ∧
    ~~~(5 : UInt64) = 18446744073709551610 ∧ (1 : UInt64) <<< 65 = 2 ∧ (12 : UInt64) >>> 66 = 3 := by simp
#check_simp True = ((3 : UInt64) < 3) ~> False
#check_simp True = ((3 : UInt64) ≤ 2) ~> False
#check_simp True = ((3 : UInt64) > 3) ~> False
#check_simp True = ((3 : UInt64) ≥ 4) ~> False
#check_simp True = ((3 : UInt64) = 4) ~> False
#check_simp True = ((3 : UInt64) ≠ 3) ~> False
#check_simp True = ((3 : UInt64) == 4) ~> False
#check_simp True = ((3 : UInt64) != 3) ~> False
#check_simp x = UInt64.ofNatLT 5 (by decide) ~> x = 5
#check_simp x = UInt64.ofNat 5 ~> x = 5
#check_simp x = UInt64.ofNat 18446744073709551617 ~> x = 1

end

section

variable (x : USize)

/- USize.toNat -/

#check_simp USize.toNat 4294967296 !~>
#check_simp USize.toNat 4294967295 ~> 4294967295
#check_simp USize.toNat (x &&& 1) ~> x.toNat % 2

end
