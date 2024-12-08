def INT32_MIN : Int := -0x80000000

#reduce INT32_MIN / -1
#eval INT32_MIN / -1
#eval INT32_MIN / -2
#eval INT32_MIN / 1
#reduce INT32_MIN % -1
#eval INT32_MIN % -1

#reduce (Int.emod (-2 : Int) 0)
#eval (Int.emod (-2 : Int) 0)

#reduce -(Int.emod (-2 : Int) 0)
#eval -(Int.emod (-2 : Int) 0)

@[noinline] def oneU8 : UInt8 := 1

#reduce (UInt8.mod oneU8 0).val.val
#eval (UInt8.mod oneU8 0)

#reduce (UInt8.mod oneU8 0).val.val
#eval (UInt8.mod oneU8 0)

@[noinline] def int_div x y := Int.ediv x y
@[noinline] def int_mod x y := Int.emod x y
@[noinline] def uint8_mod x y := UInt8.mod x y

@[noinline] def oneU16 : UInt16 := 1

#reduce (UInt16.mod oneU16 0).val.val
#eval (UInt16.mod oneU16 0)

@[noinline] def uint16_mod x y := UInt16.mod x y

@[noinline] def oneU32 : UInt32 := 1

#reduce (UInt32.mod oneU32 0).val.val
#eval (UInt32.mod oneU32 0)

@[noinline] def uint32_mod x y := UInt32.mod x y


@[noinline] def oneU64 : UInt64 := 1

#reduce (UInt64.mod oneU64 0).val.val
#eval (UInt64.mod oneU64 0)

@[noinline] def uint64_mod x y := UInt64.mod x y

@[noinline] def oneUSize : USize := 1

#eval (USize.mod oneUSize 0)

@[noinline] def usize_mod x y := USize.mod x y

def main : IO Unit := do
  IO.println <| int_div INT32_MIN (-1)
  IO.println <| int_div (-2) 0
  IO.println <| int_mod INT32_MIN (-1)
  IO.println <| int_mod (-2) 0
  IO.println <| uint8_mod 1 0
  IO.println <| uint16_mod 1 0
  IO.println <| uint32_mod 1 0
  IO.println <| uint64_mod 1 0
  IO.println <| usize_mod 1 0

#eval main
