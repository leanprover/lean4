#check Int8
#eval Int8.ofInt 20
#eval Int8.ofInt (-20)
#eval Int8.ofInt (-20)  = -20
#eval Int8.ofInt (-130) = 126
#eval (10 : Int8) ≠ (11 : Int8)
#eval (-10 : Int8) ≠ (10 : Int8)
#eval Int8.ofNat 10 = 10
#eval Int8.ofNat 130 = 130
#eval Int8.ofNat 120 = 120
#eval Int8.ofInt (-20) = -20
#eval (Int8.ofInt (-2)).toInt = -2
#eval (Int8.ofInt (-2)).toNat = 0
#eval (Int8.ofInt (10)).toNat = 10
#eval (Int8.ofInt (10)).toInt = 10
#eval Int8.ofNat (2^64) == 0
#eval Int8.ofInt (-2^64) == 0
#eval Int8.neg 10 = -10
#eval (20 : Int8) + 20 = 40
#eval (127 : Int8) + 1 = -128
#eval (-10 : Int8) + 10 = 0
#eval (1 : Int8) - 2 = -1
#eval (-128 : Int8) - 1 = 127
#eval (1 : Int8) * 120 = 120
#eval (2 : Int8) * 10 = 20
#eval (2 : Int8) * 128 = 0
#eval (-1 : Int8) * (-1) = 1
#eval (1 : Int8) * (-1) = -1
#eval (2 : Int8) * (-10) = -20
#eval (-5 : Int8) * (-5) = 25
#eval (10 : Int8) / 2 = 5
#eval (-10 : Int8) / 2 = -5
#eval (-10 : Int8) / -2 = 5
#eval (10 : Int8) / -2 = -5
#eval (10 : Int8) / 0 = 0
#eval (10 : Int8) % 1 = 0
#eval (10 : Int8) % 0 = 10
#eval (-10 : Int8) % 0 = -10
#eval (10 : Int8) % 3 = 1
#eval (-10 : Int8) % 3 = -1
#eval (-10 : Int8) % -3 = -1
#eval (10 : Int8) % -3 = 1
#eval (10 : Int8) &&& 10 = 10
#eval (-1 : Int8) &&& 1 = 1
#eval (-1 : Int8) ^^^ 123 = ~~~123
#eval (10 : Int8) ||| 10 = 10
#eval (10 : Int8) ||| 0 = 10
#eval (10 : Int8) ||| -1 = -1
#eval (16 : Int8) >>> 1 = 8
#eval (16 : Int8) >>> 16 = 16
#eval (16 : Int8) >>> 9 = 8
#eval (-16 : Int8) >>> 1 = -8
#eval (16 : Int8) <<< 1 = 32
#eval (16 : Int8) <<< 9 = 32
#eval (-16 : Int8) <<< 1 = -32
#eval (-16 : Int8) <<< 9 = -32
#eval (-16 : Int8) >>> 1 <<< 1 = -16
#eval (0 : Int8) < 1
#eval (0 : Int8) < 120
#eval (120 : Int8) > 0
#eval -1 < (0 : Int8)
#eval -120 < (0 : Int8)
#eval ¬((0 : Int8) < (0 : Int8))
#eval (0 : Int8) ≤ 1
#eval (0 : Int8) ≤ 120
#eval -1 ≤ (0 : Int8)
#eval -120 ≤ (0 : Int8)
#eval (0 : Int8) ≤ (0 : Int8)
#eval (-10 : Int8) ≥ (-10 : Int8)
#eval max (10 : Int8) 20 = 20
#eval max (10 : Int8) (-1) = 10
#eval min (10 : Int8) 20 = 10
#eval min (10 : Int8) (-1) = -1

def test {α : Type} [BEq α] (w : Nat) (ofBitVec : BitVec w → α) (ofInt : Int → α)
    (ofNat : Nat → α) : Bool := Id.run do
  let doIntTest (base : Int) (i : Int) : Bool :=
    let t := base + i
    let a := ofBitVec (BitVec.ofInt w t)
    let b := ofInt t
    a == b
  let doNatTest (base : Nat) (i : Nat) : Bool :=
    let t := base + i
    let a := ofBitVec (BitVec.ofInt w t)
    let b := ofNat t
    a == b


  let range := 2^9

  for c in [0:2*range] do
    let int := Int.ofNat c - range
    if !(doIntTest (2^256) int) then
      return false
    if !(doNatTest (2^256 - range) c) then
      return false
    if !(doIntTest (-2^256) int) then
      return false
  return true

#eval test 8 (⟨⟨·⟩⟩) Int8.ofInt Int8.ofNat

-- runtime representation
set_option trace.compiler.ir.result true in
def myId8 (x : Int8) : Int8 := x

#check Int16
#eval Int16.ofInt 20
#eval Int16.ofInt (-20)
#eval Int16.ofInt (-20) = -20
#eval 2^15 - 10 = 32758 ∧ Int16.ofInt (-(2^15) - 10) = 32758
#eval (10 : Int16) ≠ (11 : Int16)
#eval (-10 : Int16) ≠ (10 : Int16)
#eval Int16.ofNat 10 = 10
#eval 2^15 + 10 = 32778 ∧ Int16.ofNat 32778 = 32778
#eval Int16.ofNat 120 = 120
#eval Int16.ofInt (-20) = -20
#eval (Int16.ofInt (-2)).toInt = -2
#eval (Int16.ofInt (-2)).toNat = 0
#eval (Int16.ofInt (10)).toNat = 10
#eval (Int16.ofInt (10)).toInt = 10
#eval Int16.ofNat (2^64) == 0
#eval Int16.ofInt (-2^64) == 0
#eval Int16.neg 10 = -10
#eval (20 : Int16) + 20 = 40
#eval (2^15 - 1) = 32767 ∧ -2^15 = -32768 ∧ (32767 : Int16) + 1 = -32768
#eval (-10 : Int16) + 10 = 0
#eval (1 : Int16) - 2 = -1
#eval (2^15 - 1) = 32767 ∧ -2^15 = -32768 ∧ (-32768 : Int16) - 1 = 32767
#eval (1 : Int16) * 120 = 120
#eval (2 : Int16) * 10 = 20
#eval 65536 = 2^16 ∧ (2 : Int16) * 65536 = 0
#eval (-1 : Int16) * (-1) = 1
#eval (1 : Int16) * (-1) = -1
#eval (2 : Int16) * (-10) = -20
#eval (-5 : Int16) * (-5) = 25
#eval (10 : Int16) / 2 = 5
#eval (-10 : Int16) / 2 = -5
#eval (-10 : Int16) / -2 = 5
#eval (10 : Int16) / -2 = -5
#eval (10 : Int16) / 0 = 0
#eval (10 : Int16) % 1 = 0
#eval (10 : Int16) % 0 = 10
#eval (-10 : Int16) % 0 = -10
#eval (10 : Int16) % 3 = 1
#eval (-10 : Int16) % 3 = -1
#eval (-10 : Int16) % -3 = -1
#eval (10 : Int16) % -3 = 1
#eval (10 : Int16) &&& 10 = 10
#eval (-1 : Int16) &&& 1 = 1
#eval (-1 : Int16) ^^^ 123 = ~~~123
#eval (10 : Int16) ||| 10 = 10
#eval (10 : Int16) ||| 0 = 10
#eval (10 : Int16) ||| -1 = -1
#eval (16 : Int16) >>> 1 = 8
#eval (16 : Int16) >>> 16 = 16
#eval (16 : Int16) >>> (16 + 1) = 8
#eval (-16 : Int16) >>> 1 = -8
#eval (16 : Int16) <<< 1 = 32
#eval (16 : Int16) <<< (16 + 1) = 32
#eval (-16 : Int16) <<< 1 = -32
#eval (-16 : Int16) <<< (16 + 1) = -32
#eval (-16 : Int16) >>> 1 <<< 1 = -16
#eval (0 : Int16) < 1
#eval (0 : Int16) < 120
#eval (120 : Int16) > 0
#eval -1 < (0 : Int16)
#eval -120 < (0 : Int16)
#eval ¬((0 : Int16) < (0 : Int16))
#eval (0 : Int16) ≤ 1
#eval (0 : Int16) ≤ 120
#eval -1 ≤ (0 : Int16)
#eval -120 ≤ (0 : Int16)
#eval (0 : Int16) ≤ (0 : Int16)
#eval (-10 : Int16) ≥ (-10 : Int16)
#eval max (10 : Int16) 20 = 20
#eval max (10 : Int16) (-1) = 10
#eval min (10 : Int16) 20 = 10
#eval min (10 : Int16) (-1) = -1


#eval test 16 (⟨⟨·⟩⟩) Int16.ofInt Int16.ofNat

-- runtime representation
set_option trace.compiler.ir.result true in
def myId16 (x : Int16) : Int16 := x


#check Int32
#eval Int32.ofInt 20
#eval Int32.ofInt (-20)
#eval Int32.ofInt (-20) = -20
#eval 2^31 - 10 = 2147483638 ∧ Int32.ofInt (-(2^31) - 10) = 2147483638
#eval (10 : Int32) ≠ (11 : Int32)
#eval (-10 : Int32) ≠ (10 : Int32)
#eval Int32.ofNat 10 = 10
#eval 2^31 + 10 = 2147483658 ∧ Int32.ofNat 2147483658 = 2147483658
#eval Int32.ofNat 120 = 120
#eval Int32.ofInt (-20) = -20
#eval (Int32.ofInt (-2)).toInt = -2
#eval (Int32.ofInt (-2)).toNat = 0
#eval (Int32.ofInt (10)).toNat = 10
#eval (Int32.ofInt (10)).toInt = 10
#eval Int32.ofNat (2^64) == 0
#eval Int32.ofInt (-2^64) == 0
#eval Int32.neg 10 = -10
#eval (20 : Int32) + 20 = 40
#eval (2^31 - 1) = 2147483647 ∧ -2^31 = -2147483648 ∧ (2147483647 : Int32) + 1 = -2147483648
#eval (-10 : Int32) + 10 = 0
#eval (1 : Int32) - 2 = -1
#eval (2^31 - 1) = 2147483647 ∧ -2^31 = -2147483648 ∧ (-2147483648 : Int32) - 1 = 2147483647
#eval (1 : Int32) * 120 = 120
#eval (2 : Int32) * 10 = 20
#eval 4294967296 = 2^32 ∧ (2 : Int32) * 4294967296 = 0
#eval (-1 : Int32) * (-1) = 1
#eval (1 : Int32) * (-1) = -1
#eval (2 : Int32) * (-10) = -20
#eval (-5 : Int32) * (-5) = 25
#eval (10 : Int32) / 2 = 5
#eval (-10 : Int32) / 2 = -5
#eval (-10 : Int32) / -2 = 5
#eval (10 : Int32) / -2 = -5
#eval (10 : Int32) / 0 = 0
#eval (10 : Int32) % 1 = 0
#eval (10 : Int32) % 0 = 10
#eval (-10 : Int32) % 0 = -10
#eval (10 : Int32) % 3 = 1
#eval (-10 : Int32) % 3 = -1
#eval (-10 : Int32) % -3 = -1
#eval (10 : Int32) % -3 = 1
#eval (10 : Int32) &&& 10 = 10
#eval (-1 : Int32) &&& 1 = 1
#eval (-1 : Int32) ^^^ 123 = ~~~123
#eval (10 : Int32) ||| 10 = 10
#eval (10 : Int32) ||| 0 = 10
#eval (10 : Int32) ||| -1 = -1
#eval (16 : Int32) >>> 1 = 8
#eval (16 : Int32) >>> 32 = 16
#eval (16 : Int32) >>> (32 + 1) = 8
#eval (-16 : Int32) >>> 1 = -8
#eval (16 : Int32) <<< 1 = 32
#eval (16 : Int32) <<< (32 + 1) = 32
#eval (-16 : Int32) <<< 1 = -32
#eval (-16 : Int32) <<< (32 + 1) = -32
#eval (-16 : Int32) >>> 1 <<< 1 = -16
#eval (0 : Int32) < 1
#eval (0 : Int32) < 120
#eval (120 : Int32) > 0
#eval -1 < (0 : Int32)
#eval -120 < (0 : Int32)
#eval ¬((0 : Int32) < (0 : Int32))
#eval (0 : Int32) ≤ 1
#eval (0 : Int32) ≤ 120
#eval -1 ≤ (0 : Int32)
#eval -120 ≤ (0 : Int32)
#eval (0 : Int32) ≤ (0 : Int32)
#eval (-10 : Int32) ≥ (-10 : Int32)
#eval max (10 : Int32) 20 = 20
#eval max (10 : Int32) (-1) = 10
#eval min (10 : Int32) 20 = 10
#eval min (10 : Int32) (-1) = -1


#eval test 32 (⟨⟨·⟩⟩) Int32.ofInt Int32.ofNat

-- runtime representation
set_option trace.compiler.ir.result true in
def myId32 (x : Int32) : Int32 := x

#check Int64
#eval Int64.ofInt 20
#eval Int64.ofInt (-20)
#eval Int64.ofInt (-20) = -20
#eval 2^63 - 10 = 9223372036854775798 ∧ Int64.ofInt (-(2^63) - 10) = 9223372036854775798
#eval (10 : Int64) ≠ (11 : Int64)
#eval (-10 : Int64) ≠ (10 : Int64)
#eval Int64.ofNat 10 = 10
#eval 2^63 + 10 = 9223372036854775818 ∧ Int64.ofNat 9223372036854775818 = 9223372036854775818
#eval Int64.ofNat 120 = 120
#eval Int64.ofInt (-20) = -20
#eval (Int64.ofInt (-2)).toInt = -2
#eval (Int64.ofInt (-2)).toNat = 0
#eval (Int64.ofInt (10)).toNat = 10
#eval (Int64.ofInt (10)).toInt = 10
#eval Int64.ofNat (2^64) == 0
#eval Int64.ofInt (-2^64) == 0
#eval Int64.neg 10 = -10
#eval (20 : Int64) + 20 = 40
#eval (2^63 - 1) = 9223372036854775807 ∧ -2^63 = -9223372036854775808 ∧ (9223372036854775807 : Int64) + 1 = -9223372036854775808
#eval (-10 : Int64) + 10 = 0
#eval (1 : Int64) - 2 = -1
#eval (2^63 - 1) = 9223372036854775807 ∧ -2^63 = -9223372036854775808 ∧ (-9223372036854775808 : Int64) - 1 = 9223372036854775807
#eval (1 : Int64) * 120 = 120
#eval (2 : Int64) * 10 = 20
#eval 18446744073709551616 = 2^64 ∧ (2 : Int64) * 18446744073709551616 = 0
#eval (-1 : Int64) * (-1) = 1
#eval (1 : Int64) * (-1) = -1
#eval (2 : Int64) * (-10) = -20
#eval (-5 : Int64) * (-5) = 25
#eval (10 : Int64) / 2 = 5
#eval (-10 : Int64) / 2 = -5
#eval (-10 : Int64) / -2 = 5
#eval (10 : Int64) / -2 = -5
#eval (10 : Int64) / 0 = 0
#eval (10 : Int64) % 1 = 0
#eval (10 : Int64) % 0 = 10
#eval (-10 : Int64) % 0 = -10
#eval (10 : Int64) % 3 = 1
#eval (-10 : Int64) % 3 = -1
#eval (-10 : Int64) % -3 = -1
#eval (10 : Int64) % -3 = 1
#eval (10 : Int64) &&& 10 = 10
#eval (-1 : Int64) &&& 1 = 1
#eval (-1 : Int64) ^^^ 123 = ~~~123
#eval (10 : Int64) ||| 10 = 10
#eval (10 : Int64) ||| 0 = 10
#eval (10 : Int64) ||| -1 = -1
#eval (16 : Int64) >>> 1 = 8
#eval (16 : Int64) >>> 64 = 16
#eval (16 : Int64) >>> (64 + 1) = 8
#eval (-16 : Int64) >>> 1 = -8
#eval (16 : Int64) <<< 1 = 32
#eval (16 : Int64) <<< (64 + 1) = 32
#eval (-16 : Int64) <<< 1 = -32
#eval (-16 : Int64) <<< (64 + 1) = -32
#eval (-16 : Int64) >>> 1 <<< 1 = -16
#eval (0 : Int64) < 1
#eval (0 : Int64) < 120
#eval (120 : Int64) > 0
#eval -1 < (0 : Int64)
#eval -120 < (0 : Int64)
#eval ¬((0 : Int64) < (0 : Int64))
#eval (0 : Int64) ≤ 1
#eval (0 : Int64) ≤ 120
#eval -1 ≤ (0 : Int64)
#eval -120 ≤ (0 : Int64)
#eval (0 : Int64) ≤ (0 : Int64)
#eval (-10 : Int64) ≥ (-10 : Int64)
#eval max (10 : Int64) 20 = 20
#eval max (10 : Int64) (-1) = 10
#eval min (10 : Int64) 20 = 10
#eval min (10 : Int64) (-1) = -1


#eval test 64 (⟨⟨·⟩⟩) Int64.ofInt Int64.ofNat

-- runtime representation
set_option trace.compiler.ir.result true in
def myId64 (x : Int64) : Int64 := x


#check ISize
#eval ISize.ofInt 20
#eval ISize.ofInt (-20)
#eval ISize.ofInt (-20) = -20
#eval 2^63 - 10 = 9223372036854775798 ∧ ISize.ofInt (-(2^63) - 10) = 9223372036854775798
#eval (10 : ISize) ≠ (11 : ISize)
#eval (-10 : ISize) ≠ (10 : ISize)
#eval ISize.ofNat 10 = 10
#eval 2^63 + 10 = 9223372036854775818 ∧ ISize.ofNat 9223372036854775818 = 9223372036854775818
#eval ISize.ofNat 120 = 120
#eval ISize.ofInt (-20) = -20
#eval (ISize.ofInt (-2)).toInt = -2
#eval (ISize.ofInt (-2)).toNat = 0
#eval (ISize.ofInt (10)).toNat = 10
#eval (ISize.ofInt (10)).toInt = 10
#eval ISize.ofNat (2^64) == 0
#eval ISize.ofInt (-2^64) == 0
#eval ISize.neg 10 = -10
#eval (20 : ISize) + 20 = 40
#eval (2^63 - 1) = 9223372036854775807 ∧ -2^63 = -9223372036854775808 ∧ (9223372036854775807 : ISize) + 1 = -9223372036854775808
#eval (-10 : ISize) + 10 = 0
#eval (1 : ISize) - 2 = -1
#eval (2^63 - 1) = 9223372036854775807 ∧ -2^63 = -9223372036854775808 ∧ (-9223372036854775808 : ISize) - 1 = 9223372036854775807
#eval (1 : ISize) * 120 = 120
#eval (2 : ISize) * 10 = 20
#eval 18446744073709551616 = 2^64 ∧ (2 : ISize) * 18446744073709551616 = 0
#eval (-1 : ISize) * (-1) = 1
#eval (1 : ISize) * (-1) = -1
#eval (2 : ISize) * (-10) = -20
#eval (-5 : ISize) * (-5) = 25
#eval (10 : ISize) / 2 = 5
#eval (-10 : ISize) / 2 = -5
#eval (-10 : ISize) / -2 = 5
#eval (10 : ISize) / -2 = -5
#eval (10 : ISize) / 0 = 0
#eval (10 : ISize) % 1 = 0
#eval (10 : ISize) % 0 = 10
#eval (-10 : ISize) % 0 = -10
#eval (10 : ISize) % 3 = 1
#eval (-10 : ISize) % 3 = -1
#eval (-10 : ISize) % -3 = -1
#eval (10 : ISize) % -3 = 1
#eval (10 : ISize) &&& 10 = 10
#eval (-1 : ISize) &&& 1 = 1
#eval (-1 : ISize) ^^^ 123 = ~~~123
#eval (10 : ISize) ||| 10 = 10
#eval (10 : ISize) ||| 0 = 10
#eval (10 : ISize) ||| -1 = -1
#eval (16 : ISize) >>> 1 = 8
#eval (16 : ISize) >>> 64 = 16
#eval (16 : ISize) >>> (64 + 1) = 8
#eval (-16 : ISize) >>> 1 = -8
#eval (16 : ISize) <<< 1 = 32
#eval (16 : ISize) <<< (64 + 1) = 32
#eval (-16 : ISize) <<< 1 = -32
#eval (-16 : ISize) <<< (64 + 1) = -32
#eval (-16 : ISize) >>> 1 <<< 1 = -16
#eval (0 : ISize) < 1
#eval (0 : ISize) < 120
#eval (120 : ISize) > 0
#eval -1 < (0 : ISize)
#eval -120 < (0 : ISize)
#eval ¬((0 : ISize) < (0 : ISize))
#eval (0 : ISize) ≤ 1
#eval (0 : ISize) ≤ 120
#eval -1 ≤ (0 : ISize)
#eval -120 ≤ (0 : ISize)
#eval (0 : ISize) ≤ (0 : ISize)
#eval (-10 : ISize) ≥ (-10 : ISize)
#eval max (10 : ISize) 20 = 20
#eval max (10 : ISize) (-1) = 10
#eval min (10 : ISize) 20 = 10
#eval min (10 : ISize) (-1) = -1


#eval test System.Platform.numBits (⟨⟨·⟩⟩) ISize.ofInt ISize.ofNat

-- runtime representation
set_option trace.compiler.ir.result true in
def myIdSize (x : ISize) : ISize := x
