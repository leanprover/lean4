/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
open BitVec

example (h : x = (6 : BitVec 3)) : x = -2 := by
  simp; guard_target =ₛ x = 6#3; assumption
example (h : x = (5 : BitVec 3)) : x = ~~~2 := by
  simp; guard_target =ₛ x = 5#3; assumption
example (h : x = (1 : BitVec 32)) : x = BitVec.abs (-1#32) := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = (5 : BitVec 3)) : x = 2 + 3 := by
  simp; guard_target =ₛ x = 5#3; assumption
example (h : x = (1 : BitVec 3)) : x = 5 &&& 3 := by
  simp; guard_target =ₛ x = 1#3; assumption
example (h : x = (7 : BitVec 3)) : x = 5 ||| 3 := by
  simp; guard_target =ₛ x = 7#3; assumption
example (h : x = (6 : BitVec 3)) : x = 5 ^^^ 3 := by
  simp; guard_target =ₛ x = 6#3; assumption
example (h : x = (3 : BitVec 32)) : x = 5 - 2 := by
  simp; guard_target =ₛ x = 3#32; assumption
example (h : x = (10 : BitVec 32)) : x = 5 * 2 := by
  simp; guard_target =ₛ x = 10#32; assumption
example (h : x = (4 : BitVec 32)) : x = 9 / 2 := by
  simp; guard_target =ₛ x = 4#32; assumption
example (h : x = (1 : BitVec 32)) : x = 9 % 2 := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = (4 : BitVec 32)) : x = udiv 9 2 := by
  simp; guard_target =ₛ x = 4#32; assumption
example (h : x = (1 : BitVec 32)) : x = umod 9 2 := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = (4 : BitVec 32)) : x = sdiv (-9) (-2) := by
  simp; guard_target =ₛ x = 4#32; assumption
example (h : x = (1 : BitVec 32)) : x = smod (-9) 2 := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = (1 : BitVec 32)) : x = - smtUDiv 9 0 := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = (1 : BitVec 32)) : x = - srem (-9) 2 := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = (1 : BitVec 32)) : x = - smtSDiv 9 0 := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = (1 : BitVec 32)) : x = smtSDiv (-9) 0 := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = false) : x = (4#3).getLsbD 0:= by
  simp; guard_target =ₛ x = false; assumption
example (h : x = true) : x = (4#3).getLsbD 2:= by
  simp; guard_target =ₛ x = true; assumption
example (h : x = true) : x = (4#3).getMsbD 0:= by
  simp; guard_target =ₛ x = true; assumption
example (h : x = false) : x = (4#3).getMsbD 2:= by
  simp; guard_target =ₛ x = false; assumption
example (h : x = (24 : BitVec 32)) : x = 6#32 <<< 2 := by
  simp; guard_target =ₛ x = 24#32; assumption
example (h : x = (1 : BitVec 32)) : x = 6#32 >>> 2 := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = (24 : BitVec 32)) : x = BitVec.shiftLeft 6#32 2 := by
  simp; guard_target =ₛ x = 24#32; assumption
example (h : x = (1 : BitVec 32)) : x = BitVec.ushiftRight 6#32 2 := by
  simp; guard_target =ₛ x = 1#32; assumption
example (h : x = (2 : BitVec 32)) : x = - BitVec.sshiftRight (- 6#32) 2 := by
  simp; guard_target =ₛ x = 2#32; assumption
example (h : x = (5 : BitVec 3)) : x = BitVec.rotateLeft (6#3) 1 := by
  simp; guard_target =ₛ x = 5#3; assumption
example (h : x = (3 : BitVec 3)) : x = BitVec.rotateRight (6#3) 1 := by
  simp; guard_target =ₛ x = 3#3; assumption
example (h : x = (7 : BitVec 5)) : x = 1#3 ++ 3#2 := by
  simp; guard_target =ₛ x = 7#5; assumption
example (h : x = (1 : BitVec 3)) : x = BitVec.cast (by decide : 3=2+1) 1#3 := by
  simp; guard_target =ₛ x = 1#3; assumption
example (h : x = 5) : x = (2#3 + 3#3).toNat := by
  simp; guard_target =ₛ x = 5; assumption
example (h : x = -1) : x = (2#3 - 3#3).toInt := by
  simp; guard_target =ₛ x = -1; assumption
example (h : x = (1 : BitVec 3)) : x = -BitVec.ofInt 3 (-1) := by
  simp; guard_target =ₛ x = 1#3; assumption
example (h : x) : x = (1#3 < 3#3) := by
  simp; guard_target =ₛ x; assumption
example (h : x) : x = (BitVec.ult 1#3 3#3) := by
  simp; guard_target =ₛ x; assumption
example (h : ¬x) : x = (4#3 < 3#3) := by
  simp; guard_target =ₛ ¬x; assumption
example (h : x) : x = (BitVec.slt (- 4#3) 3#3) := by
  simp; guard_target =ₛ x; assumption
example (h : x) : x = (BitVec.sle (- 4#3) 3#3) := by
  simp; guard_target =ₛ x; assumption
example (h : x) : x = (3#3 > 1#3) := by
  simp; guard_target =ₛ x; assumption
example (h : ¬x) : x = (3#3 > 4#3) := by
  simp; guard_target =ₛ ¬x; assumption
example (h : x) : x = (1#3 ≤ 3#3) := by
  simp; guard_target =ₛ x; assumption
example (h : ¬x) : x = (4#3 ≤ 3#3) := by
  simp; guard_target =ₛ ¬x; assumption
example (h : ¬x) : x = (BitVec.ule 4#3 3#3) := by
  simp; guard_target =ₛ ¬x; assumption
example (h : x) : x = (3#3 ≥ 1#3) := by
  simp; guard_target =ₛ x; assumption
example (h : ¬x) : x = (3#3 ≥ 4#3) := by
  simp; guard_target =ₛ ¬x; assumption
example (h : x = (5 : BitVec 7)) : x = (5#3).setWidth' (by decide) := by
  simp; guard_target =ₛ x = 5#7; assumption
example (h : x = (80 : BitVec 7)) : x = (5#3).shiftLeftZeroExtend 4 := by
  simp; guard_target =ₛ x = 80#7; assumption
example (h : x = (5: BitVec 3)) : x = (10#5).extractLsb' 1 3 := by
  simp; guard_target =ₛ x = 5#3; assumption
example (h : x = (9: BitVec 6)) : x = (1#3).replicate 2 := by
  simp; guard_target =ₛ x = 9#6; assumption
example (h : x = (5 : BitVec 7)) : x = (5#3).zeroExtend 7 := by
  simp; guard_target =ₛ x = 5#7; assumption
example (h : -5#10 = x) : signExtend 10 (-5#8) = x := by
  simp; guard_target =ₛ1019#10 = x; assumption
example (h : 5#10 = x) : -signExtend 10 (-5#8) = x := by
  simp; guard_target =ₛ5#10 = x; assumption
example (h : 40#32 = b) : 10#32 <<< 2#32 = b := by
  simp; guard_target =ₛ 40#32 = b; assumption
example (h : 3#32 = b) : 12#32 >>> 2#32 = b := by
  simp; guard_target =ₛ 3#32 = b; assumption
example (a : BitVec 32) (h : a >>> 2 = b) : a >>> 2#32 = b := by
  simp; guard_target =ₛ a >>> 2 = b; assumption
example (a : BitVec 32) (h : a <<< 2 = b) : a <<< 2#32 = b := by
  simp; guard_target =ₛ a <<< 2 = b; assumption
example (a : BitVec 32) (h : a <<< 3 = b) : (a <<< 1#32) <<< 2#32 = b := by
  simp; guard_target =ₛ a <<< 3 = b; assumption
example (a : BitVec 32) (h : a <<< 3 = b) : (a <<< 1) <<< 2#32 = b := by
  simp; guard_target =ₛ a <<< 3 = b; assumption
example (a : BitVec 32) (h : a <<< 3 = b) : (a <<< 1) <<< 2 = b := by
  simp; guard_target =ₛ a <<< 3 = b; assumption
example (a : BitVec 32) (h : a <<< 3 = b) : (a <<< 1#32) <<< 2 = b := by
  simp; guard_target =ₛ a <<< 3 = b; assumption
example (a : BitVec 32) (h : a >>> 3 = b) : (a >>> 1#32) >>> 2#32 = b := by
  simp; guard_target =ₛ a >>> 3 = b; assumption
example (a : BitVec 32) (h : a >>> 3 = b) : (a >>> 1) >>> 2#32 = b := by
  simp; guard_target =ₛ a >>> 3 = b; assumption
example (a : BitVec 32) (h : a >>> 3 = b) : (a >>> 1) >>> 2 = b := by
  simp; guard_target =ₛ a >>> 3 = b; assumption
example (a : BitVec 32) (h : a >>> 3 = b) : (a >>> 1#32) >>> 2 = b := by
  simp; guard_target =ₛ a >>> 3 = b; assumption
example (h : False) : 1#2 = 2#2 := by
  simp; guard_target =ₛ False; exact h
example : 1#2 ≠ 2#2 := by
  simp
