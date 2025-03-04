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

#check_simp x = 2 + 3 ~> x = 5
#check_simp x = 2 * 3 ~> x = 6
#check_simp x = 2 - 3 ~> x = 255
#check_simp x = 4 / 3 ~> x = 1
#check_simp x = 5 % 3 ~> x = 2
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

#check_simp x = 2 + 3 ~> x = 5
#check_simp x = 2 * 3 ~> x = 6
#check_simp x = 2 - 3 ~> x = 65535
#check_simp x = 4 / 3 ~> x = 1
#check_simp x = 5 % 3 ~> x = 2
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

#check_simp x = 2 + 3 ~> x = 5
#check_simp x = 2 * 3 ~> x = 6
#check_simp x = 2 - 3 ~> x = 4294967295
#check_simp x = 4 / 3 ~> x = 1
#check_simp x = 5 % 3 ~> x = 2
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

#check_simp x = 2 + 3 ~> x = 5
#check_simp x = 2 * 3 ~> x = 6
#check_simp x = 2 - 3 ~> x = 18446744073709551615
#check_simp x = 4 / 3 ~> x = 1
#check_simp x = 5 % 3 ~> x = 2
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
