open BitVec

-- Basic arithmetic
#guard 1#12 + 2#12 = 3#12
#guard 3#5 * 7#5 = 0x15#5
#guard 3#4 * 7#4 = 0x05#4

#guard zeroExtend  4 0x7f#8 = 0xf#4
#guard zeroExtend 12 0x7f#8 = 0x07f#12
#guard zeroExtend 12 0x80#8 = 0x080#12
#guard zeroExtend 16 0xff#8 = 0x00ff#16

#guard signExtend  4 0x7f#8 = 0xf#4
#guard signExtend 12 0x7f#8 = 0x07f#12
#guard signExtend 12 0x80#8 = 0xf80#12
#guard signExtend 16 0xff#8 = 0xffff#16

-- Division and mod/rem

#guard 3#4 / 0 = 0
#guard 10#4 / 2 = 5

#guard 8#4 % 0 = 8
#guard 4#4 % 1 = 0
#guard 4#4 % 3 = 1
#guard 0xf#4 % (-2) = 1
#guard 0xf#4 % (-8) = 7

#guard sdiv 6#4 2 = 3#4
#guard sdiv 7#4 2 = 3#4
#guard sdiv 6#4 (-2) = -3#4
#guard sdiv 7#4 (-2) = -3#4
#guard sdiv (-6#4) 2 = -3#4
#guard sdiv (-7#4) 2 = -3#4
#guard sdiv (-6#4) (-2) = 3#4
#guard sdiv (-7#4) (-2) = 3#4

#guard srem   3#4    2  =  1
#guard srem (-4#4)   3  = -1
#guard srem ( 4#4) (-3) =  1
#guard srem (-4#4) (-3) = -1

#guard smod   3#4    2  = 1
#guard smod (-4#4)   3  =  2
#guard smod ( 4#4) (-3) = -2
#guard smod (-4#4) (-3) = -1

-- ofInt/toInt

#guard .ofInt 3 (-1) = 0b111#3
#guard .ofInt 3 0 = 0b000#3
#guard .ofInt 3 4 = 0b100#3
#guard .ofInt 3 (-2) = 0b110#3
#guard .ofInt 3 (-4) = 0b100#3

#guard (0x0#4).toInt = 0
#guard (0x7#4).toInt = 7
#guard (0x8#4).toInt = -8
#guard (0xe#4).toInt = -2

-- Bitwise operations

#guard ~~~0b1010#4 = 0b0101#4
#guard 0b1010#4 &&& 0b0110#4 = 0b0010#4
#guard 0b1010#4 ||| 0b0110#4 = 0b1110#4
#guard 0b1010#4 ^^^ 0b0110#4 = 0b1100#4

-- shift operations
#guard 0b0011#4 <<< 3 = 0b1000
#guard 0b1011#4 >>> 1 = 0b0101
#guard sshiftRight 0b1001#4 1 = 0b1100#4
#guard rotateLeft  0b0011#4 3 = 0b1001
#guard rotateRight 0b0010#4 2 = 0b1000
#guard 0xab#8 ++ 0xcd#8 = 0xabcd#16

-- get/extract

#guard !getMsbD 0b0101#4 0
#guard getMsbD 0b0101#4 1
#guard !getMsbD 0b0101#4 2
#guard getMsbD 0b0101#4 3
#guard !getMsbD 0b1111#4 4

#guard getLsbD 0b0101#4 0
#guard !getLsbD 0b0101#4 1
#guard getLsbD 0b0101#4 2
#guard !getLsbD 0b0101#4 3
#guard !getLsbD 0b1111#4 4

#guard extractLsb 3 0 0x1234#16 = 4
#guard extractLsb 7 4 0x1234#16 = 3
#guard extractLsb' 0 4 0x1234#16 = 0x4#4

/--
This tests the match compiler with bitvector literals to ensure
it can successfully generate a pattern for a bitvector literals.

This fixes a regression introduced in PR #366.
-/
def testMatch8 (i : BitVec 32) :=
  let op1 := i.extractLsb 28 25
  match op1 with
  | 0b1000#4 => some 0
  | _ => none

-- Pretty-printing

#guard toString 5#12 = "0x005#12"
#guard toString 5#13 = "0x0005#13"
#guard toString 5#12 = "0x005#12"
#guard toString 5#13 = "0x0005#13"

-- Simp

example (n w : Nat) (p : n < 2^w) : { toFin := { val := n, isLt := p } : BitVec w} = .ofNat w n := by
  simp only [ofFin_eq_ofNat]

-- Decidable quantifiers

example : ∀ v : BitVec 2, (v[1] && v[0]) = (v[0] && v[1]) := by decide

 -- `bv_decide` doesn't yet do existentials:
example : ∃ x y : BitVec 5, x ^^^ y = allOnes 5 := by decide
