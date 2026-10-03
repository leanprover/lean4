/-! Unit tests for Sym.Simp.EvalGround. -/

register_sym_simp groundSimp where
  post := ground

-- Basic arithmetic: Nat
example : 2 + 3 = 5 := by sym => simp groundSimp
example : 10 - 3 = 7 := by sym => simp groundSimp
example : 4 * 5 = 20 := by sym => simp groundSimp
example : 20 / 4 = 5 := by sym => simp groundSimp
example : 17 % 5 = 2 := by sym => simp groundSimp
example : 2 ^ 10 = 1024 := by sym => simp groundSimp
example : Nat.succ 5 = 6 := by sym => simp groundSimp
example : Nat.gcd 12 18 = 6 := by sym => simp groundSimp

-- Basic arithmetic: Int
example : (2 : Int) + 3 = 5 := by sym => simp groundSimp
example : (10 : Int) - 15 = -5 := by sym => simp groundSimp
example : (-3 : Int) * 4 = -12 := by sym => simp groundSimp
example : (-20 : Int) / 4 = -5 := by sym => simp groundSimp
example : (17 : Int) % 5 = 2 := by sym => simp groundSimp
example : (2 : Int) ^ 10 = 1024 := by sym => simp groundSimp
example : Int.gcd (-12) 18 = 6 := by sym => simp groundSimp
example : Int.tdiv 17 5 = 3 := by sym => simp groundSimp
example : Int.fdiv (-17) 5 = -4 := by sym => simp groundSimp
example : Int.tmod 17 5 = 2 := by sym => simp groundSimp
example : Int.fmod (-17) 5 = 3 := by sym => simp groundSimp
example : Int.bdiv 17 5 = 3 := by sym => simp groundSimp
example : Int.bmod 17 5 = 2 := by sym => simp groundSimp

-- Negation
example : -(-5 : Int) = 5 := by sym => simp groundSimp
example : -(3 : Int8) = -3 := by sym => simp groundSimp

-- Bitwise: Nat
example : 5 &&& 3 = 1 := by sym => simp groundSimp
example : 5 ||| 3 = 7 := by sym => simp groundSimp
example : 5 ^^^ 3 = 6 := by sym => simp groundSimp

-- Shifts: Nat
example : 1 <<< 4 = 16 := by sym => simp groundSimp
example : 16 >>> 2 = 4 := by sym => simp groundSimp

-- UInt8
example : (200 : UInt8) + 100 = 44 := by sym => simp groundSimp  -- overflow
example : (5 : UInt8) * 3 = 15 := by sym => simp groundSimp
example : (100 : UInt8) - 50 = 50 := by sym => simp groundSimp
example : -(1 : UInt8) = 255 := by sym => simp groundSimp
example : (0xFF : UInt8) &&& 0x0F = 0x0F := by sym => simp groundSimp
example : ~~~(0 : UInt8) = 255 := by sym => simp groundSimp

-- UInt16
example : (1000 : UInt16) + 2000 = 3000 := by sym => simp groundSimp
example : (100 : UInt16) * 100 = 10000 := by sym => simp groundSimp

-- UInt32
example : (100000 : UInt32) + 200000 = 300000 := by sym => simp groundSimp
example : (1 : UInt32) <<< 20 = 1048576 := by sym => simp groundSimp

-- UInt64
example : (1 : UInt64) <<< 40 = 1099511627776 := by sym => simp groundSimp

-- Int8
example : (100 : Int8) + 50 = -106 := by sym => simp groundSimp  -- overflow
example : (-128 : Int8) - 1 = 127 := by sym => simp groundSimp   -- underflow
example : -((-128) : Int8) = -128 := by sym => simp groundSimp   -- edge case

-- Int16
example : (1000 : Int16) + 2000 = 3000 := by sym => simp groundSimp

-- Int32
example : (100000 : Int32) * 100 = 10000000 := by sym => simp groundSimp

-- Int64
example : (1000000000 : Int64) * 1000 = 1000000000000 := by sym => simp groundSimp

-- Rat
example : (1 : Rat) / 2 + 1 / 3 = 5 / 6 := by sym => simp groundSimp
example : (2 : Rat) / 3 * 3 / 4 = 1 / 2 := by sym => simp groundSimp
example : (1 : Rat) / 2 - 1 / 3 = 1 / 6 := by sym => simp groundSimp
example : ((2 : Rat) / 3)⁻¹ = 3 / 2 := by sym => simp groundSimp

-- Fin
example : (3 : Fin 5) + 4 = 2 := by sym => simp groundSimp  -- wraps
example : (2 : Fin 10) * 3 = 6 := by sym => simp groundSimp
example : -(1 : Fin 5) = 4 := by sym => simp groundSimp

-- Fin operations
example : (3 : Fin 5).succ = 4 := by sym => simp groundSimp
example : (3 : Fin 5).castSucc = 3 := by sym => simp groundSimp
example : Fin.last 4 = 4 := by sym => simp groundSimp
example : (1 : Fin 5).rev = 3 := by sym => simp groundSimp
example : (3 : Fin 5).pred (by decide) = 2 := by sym => simp groundSimp
example : (2 : Fin 5).castAdd 3 = 2 := by sym => simp groundSimp
example : (2 : Fin 5).addNat 3 = 5 := by sym => simp groundSimp
example : Fin.natAdd 3 (2 : Fin 5) = 5 := by sym => simp groundSimp
example : (2 : Fin 5).castLT (by decide : (2 : Fin 5).val < 3) = 2 := by sym => simp groundSimp
example : Fin.castLE (by decide : 5 ≤ 7) (2 : Fin 5) = 2 := by sym => simp groundSimp
example : Fin.subNat 2 (4 : Fin 5) (by decide) = 2 := by sym => simp groundSimp
example : (⟨2, by decide⟩ : Fin 5) = 2 := by sym => simp groundSimp
example : Fin.ofNat 5 7 = 2 := by sym => simp groundSimp
example : (7 : Fin 5) = 2 := by sym => simp groundSimp
example : (3 : Fin 5).val = 3 := by sym => simp groundSimp
-- Out-of-range literals are normalized inside other operations too
example : (7 : Fin 5).succ = 3 := by sym => simp groundSimp

-- BitVec
example : (2 : BitVec 8) + 3 = 5 := by sym => simp groundSimp
example : (10 : BitVec 8) - 3 = 7 := by sym => simp groundSimp
example : (3 : BitVec 8) - 10 = 249 := by sym => simp groundSimp  -- underflow
example : (4 : BitVec 8) * 5 = 20 := by sym => simp groundSimp
example : (20 : BitVec 8) / 3 = 6 := by sym => simp groundSimp
example : (20 : BitVec 8) % 3 = 2 := by sym => simp groundSimp
example : -(1 : BitVec 8) = 255 := by sym => simp groundSimp
example : (0x0F : BitVec 8) &&& 0x3C = 0x0C := by sym => simp groundSimp
example : (0x0F : BitVec 8) ||| 0x30 = 0x3F := by sym => simp groundSimp
example : (0xFF : BitVec 8) ^^^ 0xAA = 0x55 := by sym => simp groundSimp
example : ~~~(0x0F : BitVec 8) = 0xF0 := by sym => simp groundSimp
example : (1 : BitVec 8) <<< 4 = 16 := by sym => simp groundSimp
example : (0x80 : BitVec 8) >>> 4 = 0x08 := by sym => simp groundSimp
example : (100 : BitVec 8) + 200 = 44 := by sym => simp groundSimp  -- overflow

-- BitVec: append / indexing
example : ((0xAB : BitVec 8) ++ (0xCD : BitVec 8)).toNat = 0xABCD := by sym => simp groundSimp
example : (0xAA : BitVec 8)[1] = true := by sym => simp groundSimp

-- BitVec: named shift/rotate functions
example : BitVec.shiftLeft (1 : BitVec 8) 4 = 16 := by sym => simp groundSimp
example : BitVec.ushiftRight (0x80 : BitVec 8) 4 = 0x08 := by sym => simp groundSimp
example : BitVec.sshiftRight (0x80 : BitVec 8) 4 = 0xF8 := by sym => simp groundSimp
example : BitVec.sshiftRight' (0x80 : BitVec 8) (4 : BitVec 8) = 0xF8 := by sym => simp groundSimp
example : BitVec.rotateLeft (0x81 : BitVec 8) 1 = 0x03 := by sym => simp groundSimp
example : BitVec.rotateRight (0x81 : BitVec 8) 1 = 0xC0 := by sym => simp groundSimp

-- BitVec: division / remainder variants
example : BitVec.udiv (20 : BitVec 8) 3 = 6 := by sym => simp groundSimp
example : BitVec.umod (20 : BitVec 8) 3 = 2 := by sym => simp groundSimp
example : BitVec.sdiv (0xEC : BitVec 8) 3 = 0xFA := by sym => simp groundSimp   -- -20 / 3 = -6
example : BitVec.smod (0xEC : BitVec 8) 3 = 1 := by sym => simp groundSimp
example : BitVec.srem (0xEC : BitVec 8) 3 = 0xFE := by sym => simp groundSimp   -- -20 rem 3 = -2
example : BitVec.smtUDiv (20 : BitVec 8) 0 = 0xFF := by sym => simp groundSimp  -- division by zero
example : BitVec.smtSDiv (0xEC : BitVec 8) 3 = 0xFA := by sym => simp groundSimp

-- BitVec: abs / bit-counting
example : BitVec.abs (0xFB : BitVec 8) = 5 := by sym => simp groundSimp  -- |-5|
example : BitVec.clz (0x01 : BitVec 8) = 7 := by sym => simp groundSimp
example : BitVec.cpop (0xF0 : BitVec 8) = 4 := by sym => simp groundSimp

-- BitVec: bit access
example : (0xAA : BitVec 8).getLsbD 1 = true := by sym => simp groundSimp
example : (0xAA : BitVec 8).getMsbD 0 = true := by sym => simp groundSimp

-- BitVec: width-changing operations
example : (0xFF : BitVec 8).setWidth 4 = 0xF := by sym => simp groundSimp
example : (0xF : BitVec 4).zeroExtend 8 = 0x0F := by sym => simp groundSimp
example : (0xF : BitVec 4).signExtend 8 = 0xFF := by sym => simp groundSimp
example : BitVec.setWidth' (n := 4) (w := 8) (by omega) (0x0F : BitVec 4) = 0x0F := by sym => simp groundSimp
example : BitVec.cast (n := 4) (m := 4) rfl (0x0F : BitVec 4) = 0x0F := by sym => simp groundSimp
example : (BitVec.shiftLeftZeroExtend (0x0F : BitVec 4) 4).toNat = 0xF0 := by sym => simp groundSimp
example : BitVec.extractLsb' 4 4 (0xAB : BitVec 8) = 0xA := by sym => simp groundSimp
example : (BitVec.replicate 2 (0x0F : BitVec 4)).toNat = 0xFF := by sym => simp groundSimp
example : BitVec.allOnes 8 = 0xFF := by sym => simp groundSimp

-- BitVec: Nat/Int/Fin conversions
example : (200 : BitVec 8).toNat = 200 := by sym => simp groundSimp
example : BitVec.ofNat 8 300 = 44 := by sym => simp groundSimp  -- overflow
example : (0xFF : BitVec 8).toInt = -1 := by sym => simp groundSimp
example : BitVec.ofInt 8 (-1) = 0xFF := by sym => simp groundSimp
example : (5 : BitVec 8).toFin = (5 : Fin 256) := by sym => simp groundSimp
example : BitVec.ofFin (w := 8) (5 : Fin 256) = 5 := by sym => simp groundSimp

-- BitVec: fixed-width conversions
example : (-1 : Int8).toBitVec = 0xFF := by sym => simp groundSimp
example : (-1 : Int16).toBitVec = 0xFFFF := by sym => simp groundSimp
example : (-1 : Int32).toBitVec = 0xFFFFFFFF := by sym => simp groundSimp
example : (-1 : Int64).toBitVec = 0xFFFFFFFFFFFFFFFF := by sym => simp groundSimp
example : (255 : UInt8).toBitVec = 0xFF := by sym => simp groundSimp
example : (65535 : UInt16).toBitVec = 0xFFFF := by sym => simp groundSimp
example : (4294967295 : UInt32).toBitVec = 0xFFFFFFFF := by sym => simp groundSimp
example : (18446744073709551615 : UInt64).toBitVec = 0xFFFFFFFFFFFFFFFF := by sym => simp groundSimp

-- Predicates: Nat
example : (2 < 3) = True := by sym => simp groundSimp
example : (5 < 3) = False := by sym => simp groundSimp
example : (3 ≤ 3) = True := by sym => simp groundSimp
example : (4 ≤ 3) = False := by sym => simp groundSimp
example : (5 > 3) = True := by sym => simp groundSimp
example : (2 > 3) = False := by sym => simp groundSimp
example : (3 ≥ 3) = True := by sym => simp groundSimp
example : (2 ≥ 3) = False := by sym => simp groundSimp
example : (5 = 5) = True := by sym => simp groundSimp
example : (5 = 6) = False := by sym => simp groundSimp
example : (5 ≠ 6) = True := by sym => simp groundSimp
example : (5 ≠ 5) = False := by sym => simp groundSimp

-- Predicates: Int
example : ((-3 : Int) < 2) = True := by sym => simp groundSimp
example : ((5 : Int) < -3) = False := by sym => simp groundSimp
example : ((-3 : Int) ≤ -3) = True := by sym => simp groundSimp
example : ((2 : Int) = 2) = True := by sym => simp groundSimp
example : ((2 : Int) ≠ 3) = True := by sym => simp groundSimp

-- Predicates: Rat
example : ((1 : Rat) / 2 < 2 / 3) = True := by sym => simp groundSimp
example : ((1 : Rat) / 2 = 2 / 4) = True := by sym => simp groundSimp

-- Predicates: String
example : "hello" < "world" := by sym => simp groundSimp
example : "a" ≤ "a" := by sym => simp groundSimp
example : ¬ "a" > "b" := by sym => simp groundSimp
example : "a" = "a" := by sym => simp groundSimp
example : "a" ≠ "b" := by sym => simp groundSimp

-- String operations
example : "abc".push 'd' = "abcd" := by sym => simp groundSimp
example : "".push 'a' = "a" := by sym => simp groundSimp
example : String.singleton 'a' = "a" := by sym => simp groundSimp
example : ("ab".push 'c').push 'd' = "abcd" := by sym => simp groundSimp
example : "ab" ++ String.singleton 'c' = "abc" := by sym => simp groundSimp

-- Predicates: Char
example : 'h' < 'w' := by sym => simp groundSimp
example : 'a' ≤ 'a' := by sym => simp groundSimp
example : ¬ 'a' > 'b' := by sym => simp groundSimp
example : 'a' = 'a' := by sym => simp groundSimp
example : 'a' ≠ 'b' := by sym => simp groundSimp
example : ('a' == 'b') = false := by sym => simp groundSimp
example : ('a' != 'b') = true := by sym => simp groundSimp

-- Char operations
example : 'a'.toNat = 97 := by sym => simp groundSimp
example : 'a'.toUpper = 'A' := by sym => simp groundSimp
example : 'A'.toLower = 'a' := by sym => simp groundSimp
example : '1'.toUpper = '1' := by sym => simp groundSimp
example : 'a'.isAlpha = true := by sym => simp groundSimp
example : '1'.isAlpha = false := by sym => simp groundSimp
example : '1'.isDigit = true := by sym => simp groundSimp
example : 'a'.isDigit = false := by sym => simp groundSimp
example : ' '.isWhitespace = true := by sym => simp groundSimp
example : 'a'.isWhitespace = false := by sym => simp groundSimp
example : 'A'.isUpper = true := by sym => simp groundSimp
example : 'a'.isUpper = false := by sym => simp groundSimp
example : 'a'.isLower = true := by sym => simp groundSimp
example : 'A'.isLower = false := by sym => simp groundSimp
example : 'a'.isAlphanum = true := by sym => simp groundSimp
example : '_'.isAlphanum = false := by sym => simp groundSimp
example : toString 'a' = "a" := by sym => simp groundSimp
-- `Char.ofNat` applied to a numeral is not a character literal
example : Char.ofNat 97 = 'a' := by sym => simp groundSimp
example : (Char.ofNat 97).toNat = 97 := by sym => simp groundSimp
-- Invalid code points
example : Char.ofNat 0xd800 = '\x00' := by sym => simp groundSimp
example : Char.ofNat 0x110000 = '\x00' := by sym => simp groundSimp

-- Predicates: Fixed-width
example : ((100 : UInt8) < 200) = True := by sym => simp groundSimp
example : ((-50 : Int8) < 50) = True := by sym => simp groundSimp
example : ((1000 : UInt16) ≤ 1000) = True := by sym => simp groundSimp
example : ((-50 : Int8) > 50) = False := by sym => simp groundSimp

-- Predicates: BitVec
example : ((5 : BitVec 8) < 10) = True := by sym => simp groundSimp
example : ((5 : BitVec 8) ≤ 5) = True := by sym => simp groundSimp
example : ((255 : BitVec 8) = 255) = True := by sym => simp groundSimp
example : ((5 : BitVec 8) ≠ 6) = True := by sym => simp groundSimp
example : BitVec.ult (5 : BitVec 8) 10 = true := by sym => simp groundSimp
example : BitVec.ule (5 : BitVec 8) 5 = true := by sym => simp groundSimp
example : BitVec.slt (0xFF : BitVec 8) 1 = true := by sym => simp groundSimp  -- -1 < 1 (signed)
example : BitVec.sle (0xFF : BitVec 8) 0xFF = true := by sym => simp groundSimp

-- Predicates: Fin
example : ((2 : Fin 5) < 3) = True := by sym => simp groundSimp
example : ((4 : Fin 5) ≤ 4) = True := by sym => simp groundSimp

-- Dvd
example : (3 ∣ 12) = True := by sym => simp groundSimp
example : (5 ∣ 12) = False := by sym => simp groundSimp
example : ((3 : Int) ∣ -12) = True := by sym => simp groundSimp
example : ((5 : Int) ∣ 12) = False := by sym => simp groundSimp

-- BEq / bne (Bool results)
example : ((5 : Nat) == 5) = true := by sym => simp groundSimp
example : ((5 : Nat) == 6) = false := by sym => simp groundSimp
example : ((5 : Nat) != 6) = true := by sym => simp groundSimp
example : ((5 : Nat) != 5) = false := by sym => simp groundSimp
example : ((5 : Int) == 5) = true := by sym => simp groundSimp
example : ((0xFF : BitVec 8) == 255) = true := by sym => simp groundSimp
example : ((0xFF : BitVec 8) != 0) = true := by sym => simp groundSimp

-- Bool
example : Bool.and true false = false := by sym => simp groundSimp
example : Bool.or false true = true := by sym => simp groundSimp
example : Bool.not true = false := by sym => simp groundSimp
example : (true == false) = false := by sym => simp groundSimp
example : (true != false) = true := by sym => simp groundSimp
example : (true = true) = True := by sym => simp groundSimp

-- Identity fast path (isSameExpr)
example : ∀ n : Nat, (n = n) = True := by intro n; sym => simp groundSimp
example : ∀ n : Nat, (n ≠ n) = False := by intro n; sym => simp groundSimp

-- Edge cases
example : 0 / 0 = 0 := by sym => simp groundSimp  -- Nat division by zero
example : 5 % 0 = 5 := by sym => simp groundSimp  -- Nat mod by zero
example : 0 ^ 0 = 1 := by sym => simp groundSimp  -- 0^0 = 1 in Lean

theorem ex₁ : (2 / 3 : Rat) + 2 / 3 = 8 / 6 := by sym => simp groundSimp

/--
info: theorem ex₁._proof_1_1 : 2 / 3 + 2 / 3 = 8 / 6 :=
Eq.mpr (Eq.trans (congr (congrArg Eq (Eq.refl (4 / 3))) (Eq.refl (4 / 3))) (eq_self (4 / 3))) True.intro
-/
#guard_msgs in
#print ex₁._proof_1_1

theorem ex₂ : (- 2) = (- (- (- 2))) := by sym => simp groundSimp

/--
info: theorem ex₂._proof_1_1 : -2 = - - -2 :=
Eq.mpr (Eq.trans (congrArg (Eq (-2)) (congrArg Neg.neg (Eq.refl 2))) (eq_self (-2))) True.intro
-/
#guard_msgs in
#print ex₂._proof_1_1
