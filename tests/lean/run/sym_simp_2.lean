import Lean
open Lean Meta Elab Tactic

elab "sym_simp" : tactic => do
  let methods : Sym.Simp.Methods := { post := Sym.Simp.evalGround }
  liftMetaTactic1 <| Sym.simpWith (Sym.simp · methods)

-- Basic arithmetic: Nat
example : 2 + 3 = 5 := by sym_simp
example : 10 - 3 = 7 := by sym_simp
example : 4 * 5 = 20 := by sym_simp
example : 20 / 4 = 5 := by sym_simp
example : 17 % 5 = 2 := by sym_simp
example : 2 ^ 10 = 1024 := by sym_simp
example : Nat.succ 5 = 6 := by sym_simp
example : Nat.gcd 12 18 = 6 := by sym_simp

-- Basic arithmetic: Int
example : (2 : Int) + 3 = 5 := by sym_simp
example : (10 : Int) - 15 = -5 := by sym_simp
example : (-3 : Int) * 4 = -12 := by sym_simp
example : (-20 : Int) / 4 = -5 := by sym_simp
example : (17 : Int) % 5 = 2 := by sym_simp
example : (2 : Int) ^ 10 = 1024 := by sym_simp
example : Int.gcd (-12) 18 = 6 := by sym_simp
example : Int.tdiv 17 5 = 3 := by sym_simp
example : Int.fdiv (-17) 5 = -4 := by sym_simp
example : Int.tmod 17 5 = 2 := by sym_simp
example : Int.fmod (-17) 5 = 3 := by sym_simp
example : Int.bdiv 17 5 = 3 := by sym_simp
example : Int.bmod 17 5 = 2 := by sym_simp

-- Negation
example : -(-5 : Int) = 5 := by sym_simp
example : -(3 : Int8) = -3 := by sym_simp

-- Bitwise: Nat
example : 5 &&& 3 = 1 := by sym_simp
example : 5 ||| 3 = 7 := by sym_simp
example : 5 ^^^ 3 = 6 := by sym_simp

-- Shifts: Nat
example : 1 <<< 4 = 16 := by sym_simp
example : 16 >>> 2 = 4 := by sym_simp

-- UInt8
example : (200 : UInt8) + 100 = 44 := by sym_simp  -- overflow
example : (5 : UInt8) * 3 = 15 := by sym_simp
example : (100 : UInt8) - 50 = 50 := by sym_simp
example : -(1 : UInt8) = 255 := by sym_simp
example : (0xFF : UInt8) &&& 0x0F = 0x0F := by sym_simp
example : ~~~(0 : UInt8) = 255 := by sym_simp

-- UInt16
example : (1000 : UInt16) + 2000 = 3000 := by sym_simp
example : (100 : UInt16) * 100 = 10000 := by sym_simp

-- UInt32
example : (100000 : UInt32) + 200000 = 300000 := by sym_simp
example : (1 : UInt32) <<< 20 = 1048576 := by sym_simp

-- UInt64
example : (1 : UInt64) <<< 40 = 1099511627776 := by sym_simp

-- Int8
example : (100 : Int8) + 50 = -106 := by sym_simp  -- overflow
example : (-128 : Int8) - 1 = 127 := by sym_simp   -- underflow
example : -((-128) : Int8) = -128 := by sym_simp   -- edge case

-- Int16
example : (1000 : Int16) + 2000 = 3000 := by sym_simp

-- Int32
example : (100000 : Int32) * 100 = 10000000 := by sym_simp

-- Int64
example : (1000000000 : Int64) * 1000 = 1000000000000 := by sym_simp

-- Rat
example : (1 : Rat) / 2 + 1 / 3 = 5 / 6 := by sym_simp
example : (2 : Rat) / 3 * 3 / 4 = 1 / 2 := by sym_simp
example : (1 : Rat) / 2 - 1 / 3 = 1 / 6 := by sym_simp
example : ((2 : Rat) / 3)⁻¹ = 3 / 2 := by sym_simp

-- Fin
example : (3 : Fin 5) + 4 = 2 := by sym_simp  -- wraps
example : (2 : Fin 10) * 3 = 6 := by sym_simp
example : -(1 : Fin 5) = 4 := by sym_simp

-- BitVec
example : (2 : BitVec 8) + 3 = 5 := by sym_simp
example : (0x0F : BitVec 8) &&& 0x3C = 0x0C := by sym_simp
example : (0x0F : BitVec 8) ||| 0x30 = 0x3F := by sym_simp
example : (0xFF : BitVec 8) ^^^ 0xAA = 0x55 := by sym_simp
example : ~~~(0x0F : BitVec 8) = 0xF0 := by sym_simp
example : (1 : BitVec 8) <<< 4 = 16 := by sym_simp
example : (0x80 : BitVec 8) >>> 4 = 0x08 := by sym_simp
example : (100 : BitVec 8) + 200 = 44 := by sym_simp  -- overflow

-- Predicates: Nat
example : (2 < 3) = True := by sym_simp
example : (5 < 3) = False := by sym_simp
example : (3 ≤ 3) = True := by sym_simp
example : (4 ≤ 3) = False := by sym_simp
example : (5 > 3) = True := by sym_simp
example : (2 > 3) = False := by sym_simp
example : (3 ≥ 3) = True := by sym_simp
example : (2 ≥ 3) = False := by sym_simp
example : (5 = 5) = True := by sym_simp
example : (5 = 6) = False := by sym_simp
example : (5 ≠ 6) = True := by sym_simp
example : (5 ≠ 5) = False := by sym_simp

-- Predicates: Int
example : ((-3 : Int) < 2) = True := by sym_simp
example : ((5 : Int) < -3) = False := by sym_simp
example : ((-3 : Int) ≤ -3) = True := by sym_simp
example : ((2 : Int) = 2) = True := by sym_simp
example : ((2 : Int) ≠ 3) = True := by sym_simp

-- Predicates: Rat
example : ((1 : Rat) / 2 < 2 / 3) = True := by sym_simp
example : ((1 : Rat) / 2 = 2 / 4) = True := by sym_simp

-- Predicates: String
example : "hello" < "world" := by sym_simp
example : "a" ≤ "a" := by sym_simp
example : ¬ "a" > "b" := by sym_simp
example : "a" = "a" := by sym_simp
example : "a" ≠ "b" := by sym_simp

-- Predicates: Char
example : 'h' < 'w' := by sym_simp
example : 'a' ≤ 'a' := by sym_simp
example : ¬ 'a' > 'b' := by sym_simp
example : 'a' = 'a' := by sym_simp
example : 'a' ≠ 'b' := by sym_simp

-- Predicates: Fixed-width
example : ((100 : UInt8) < 200) = True := by sym_simp
example : ((-50 : Int8) < 50) = True := by sym_simp
example : ((1000 : UInt16) ≤ 1000) = True := by sym_simp
example : ((-50 : Int8) > 50) = False := by sym_simp

-- Predicates: BitVec
example : ((5 : BitVec 8) < 10) = True := by sym_simp
example : ((255 : BitVec 8) = 255) = True := by sym_simp

-- Predicates: Fin
example : ((2 : Fin 5) < 3) = True := by sym_simp
example : ((4 : Fin 5) ≤ 4) = True := by sym_simp

-- Dvd
example : (3 ∣ 12) = True := by sym_simp
example : (5 ∣ 12) = False := by sym_simp
example : ((3 : Int) ∣ -12) = True := by sym_simp
example : ((5 : Int) ∣ 12) = False := by sym_simp

-- BEq / bne (Bool results)
example : ((5 : Nat) == 5) = true := by sym_simp
example : ((5 : Nat) == 6) = false := by sym_simp
example : ((5 : Nat) != 6) = true := by sym_simp
example : ((5 : Nat) != 5) = false := by sym_simp
example : ((5 : Int) == 5) = true := by sym_simp
example : ((0xFF : BitVec 8) == 255) = true := by sym_simp

-- Identity fast path (isSameExpr)
example : ∀ n : Nat, (n = n) = True := by intro n; sym_simp
example : ∀ n : Nat, (n ≠ n) = False := by intro n; sym_simp

-- Edge cases
example : 0 / 0 = 0 := by sym_simp  -- Nat division by zero
example : 5 % 0 = 5 := by sym_simp  -- Nat mod by zero
example : 0 ^ 0 = 1 := by sym_simp  -- 0^0 = 1 in Lean

theorem ex₁ : (2 / 3 : Rat) + 2 / 3 = 8 / 6 := by sym_simp

/--
info: theorem ex₁ : 2 / 3 + 2 / 3 = 8 / 6 :=
Eq.mpr (Eq.trans (congr (congrArg Eq (Eq.refl (4 / 3))) (Eq.refl (4 / 3))) (eq_self (4 / 3))) True.intro
-/
#guard_msgs in
#print ex₁

theorem ex₂ : (- 2) = (- (- (- 2))) := by sym_simp

/--
info: theorem ex₂ : -2 = - - -2 :=
Eq.mpr (Eq.trans (congrArg (Eq (-2)) (congrArg Neg.neg (Eq.refl 2))) (eq_self (-2))) True.intro
-/
#guard_msgs in
#print ex₂
