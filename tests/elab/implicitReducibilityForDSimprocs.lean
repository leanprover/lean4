import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

set_option allowUnsafeReducibility true in
attribute [implicit_reducible]
  Char.ofNat Char.ofNatAux
  UInt32.ofNat UInt32.toNat
  UInt64.ofNat UInt64.toNat
  BitVec.ofNat BitVec.ofNatLT
  Char.toNat

  -- for BitVec
  BitVec.abs BitVec.allOnes BitVec.and BitVec.append BitVec.cast BitVec.clz BitVec.clzAuxRec BitVec.cpop BitVec.cpopNatRec BitVec.extractLsb' BitVec.getLsb BitVec.not BitVec.or BitVec.replicate BitVec.rotateLeft BitVec.rotateLeftAux
  BitVec.rotateRight BitVec.rotateRightAux BitVec.setWidth BitVec.setWidth' BitVec.shiftLeft BitVec.shiftLeftZeroExtend BitVec.signExtend BitVec.sle BitVec.slt BitVec.smod BitVec.smtSDiv BitVec.smtUDiv BitVec.sshiftRight BitVec.ule
  BitVec.ult BitVec.ushiftRight BitVec.xor BitVec.zeroExtend
  Bool.toNat
  Int.shiftRight
  cond

  -- for SInt
  BitVec.mul BitVec.add BitVec.sub BitVec.neg
  BitVec.smod BitVec.srem BitVec.umod
  BitVec.sdiv BitVec.getLsbD BitVec.getMsbD BitVec.msb BitVec.udiv
  BitVec.ofInt BitVec.toInt
  Int.add Int.neg Int.negOfNat Int.sub Int.subNatNat
  Int.toNat Int.natAbs Int.emod
  Int.bdiv Int.bmod Int.decEq Int.decNonneg Int.ediv Int.fdiv Int.fmod Int.mul Int.pow Int.tdiv Int.tmod
  Int8.mul Int8.add Int8.sub Int8.div Int8.mod Int8.ofIntLE Int8.ofInt Int8.ofUInt8
  Int8.neg Int8.toInt Int8.toNatClampNeg
  Int16.mul Int16.add Int16.sub Int16.div Int16.mod Int16.ofIntLE Int16.ofInt Int16.ofUInt16
  Int16.neg Int16.toInt Int16.toNatClampNeg
  Int32.mul Int32.add Int32.sub Int32.div Int32.mod Int32.ofIntLE Int32.ofInt Int32.ofUInt32
  Int32.neg Int32.toInt Int32.toNatClampNeg
  Int64.mul Int64.add Int64.sub Int64.div Int64.mod Int64.ofIntLE Int64.ofInt Int64.ofUInt64
  Int64.neg Int64.toInt Int64.toNatClampNeg
  ISize.mul ISize.add ISize.sub ISize.div ISize.mod
  ISize.neg ISize.toInt ISize.toNatClampNeg

  BitVec.add BitVec.decEq BitVec.mul BitVec.sub
  UInt8.add UInt8.decEq UInt8.div UInt8.mod UInt8.mul UInt8.ofNat UInt8.ofNatLT UInt8.sub UInt8.toNat
  UInt16.add UInt16.decEq UInt16.div UInt16.mod UInt16.mul UInt16.ofNat UInt16.ofNatLT UInt16.sub UInt16.toNat
  UInt32.add UInt32.decEq UInt32.div UInt32.mod UInt32.mul UInt32.ofNat UInt32.ofNatLT UInt32.sub UInt32.toNat
  UInt64.add UInt64.decEq UInt64.div UInt64.mod UInt64.mul UInt64.ofNat UInt64.ofNatLT UInt64.sub UInt64.toNat

  -- necessary for division
  Bool.and Bool.not
  Nat.testBit
  decide bne

  Array.get!Internal Array.getInternal
  List.get

  Array.empty Array.emptyWithCapacity Array.push
  Bool.or
  ByteArray.append ByteArray.empty ByteArray.emptyWithCapacity ByteArray.push
  Char.isAlpha Char.isAlphanum Char.isDigit Char.isLower Char.isUpper Char.isWhitespace Char.ofNat Char.ofNatAux Char.toLower Char.toNat Char.toString Char.toUpper
  Fin.add Fin.addNat Fin.castAdd Fin.castLE Fin.castLT Fin.castSucc Fin.div Fin.land Fin.last Fin.lor Fin.mod Fin.mul Fin.natAdd Fin.ofNat Fin.pred Fin.rev Fin.shiftLeft Fin.shiftRight Fin.sub Fin.subNat Fin.succ Fin.xor
  List.append List.concat List.flatMap List.flatten List.map List.replicate List.toByteArray List.toByteArray.loop List.utf8Encode
  String.append String.decEq String.ofList String.push String.singleton String.utf8EncodeChar
  Array.toList ByteArray.get ByteArray.utf8Decode? ByteArray.utf8Decode?.go ByteArray.utf8Decode?.go._unary ByteArray.utf8DecodeChar? ByteArray.utf8DecodeChar?.assemble₁ ByteArray.utf8DecodeChar?.parseFirstByte Char.utf8Size
  Option.get String.Internal.toArray String.toList UInt8.land UInt8.toUInt32 WellFounded.Nat.eager WellFounded.Nat.fix WellFounded.Nat.fix.go

section Array

example : #[1, 2, 3][1] = 2 := by with_implicit rfl
example : #[1, 2, 3][1]? = some 2 := by with_implicit rfl
example : #[1, 2, 3][1]! = 2 := by with_implicit rfl

end Array

section BitVec

example : - 0#3 = 0#3 := by with_implicit rfl
example : ~~~ 0#3 = -1#3 := by with_implicit rfl
example : BitVec.abs (-1#3) = 1#3 := by with_implicit rfl
example : 3#3 &&& 5#3 = 1#3 := by with_implicit rfl
example : 3#3 ||| 5#3 = 7#3 := by with_implicit rfl
example : 3#3 ^^^ 5#3 = 6#3 := by with_implicit rfl
example : 3#8 + 5#8 = 8#8 := by with_implicit rfl
example : 5#8 - 3#8 = 2#8 := by with_implicit rfl
example : 3#8 * 5#8 = 15#8 := by with_implicit rfl
example : 13#8 / 5#8 = 2#8 := by with_implicit rfl
example : 13#8 % 5#8 = 3#8 := by with_implicit rfl
example : BitVec.udiv 13#8 5#8 = 2#8 := by with_implicit rfl
example : BitVec.umod 13#8 5#8 = 3#8 := by with_implicit rfl
example : BitVec.smtUDiv 13#8 5#8 = 2#8 := by with_implicit rfl
example : BitVec.smod 13#8 5#8 = 3#8 := by with_implicit rfl
example : BitVec.srem 13#8 5#8 = 3#8 := by with_implicit rfl
example : BitVec.sdiv 13#8 5#8 = 2#8 := by with_implicit rfl
example : BitVec.smtSDiv 13#8 5#8 = 2#8 := by with_implicit rfl
example : BitVec.getLsbD 13#8 0 = true := by with_implicit rfl
example : BitVec.getMsbD 13#8 0 = false := by with_implicit rfl
example : BitVec.clz 13#8 = 4#8 := by with_implicit rfl
example : BitVec.cpop 13#8 = 3#8 := by with_implicit rfl
example : (13#8)[0] = true := by with_implicit rfl
example : BitVec.shiftLeft 13#8 1 = 26#8 := by with_implicit rfl
example : BitVec.ushiftRight 13#8 1 = 6#8 := by with_implicit rfl
example : BitVec.sshiftRight 13#8 1 = 6#8 := by with_implicit rfl
example : 13#8 <<< 1 = 26#8 := by with_implicit rfl
example : 13#8 <<< 1#3 = 26#8 := by with_implicit rfl
example : 13#8 >>> 1 = 6#8 := by with_implicit rfl
example : 13#8 >>> 1#3 = 6#8 := by with_implicit rfl
example : BitVec.rotateLeft 13#8 1 = 26#8 := by with_implicit rfl
example : BitVec.rotateRight 13#8 1 = 134#8 := by with_implicit rfl
example : 1#4 ++ 1#4 = 17#8 := by with_implicit rfl
-- TODO: test case for `reduceCast`?
example : (13#8).toNat = 13 := by with_implicit rfl
example : (13#8).toInt = 13 := by with_implicit rfl
example : BitVec.ofInt 8 13 = 13#8 := by with_implicit rfl
example : BitVec.ofNat 8 13 = 13#8 := by with_implicit rfl
example : (13#8 == 12#8) = false := by with_implicit rfl
example : (13#8 != 12#8) = true := by with_implicit rfl
example : BitVec.ult 12#8 13#8 = true := by with_implicit rfl
example : BitVec.ule 12#8 13#8 = true := by with_implicit rfl
example : BitVec.slt (-1#8) (0#8) = true := by with_implicit rfl
example : BitVec.sle (-1#8) (0#8) = true := by with_implicit rfl
example : BitVec.setWidth' (show 2 ≤ 4 by grind) 1#2 = 1#4 := by with_implicit rfl
example : BitVec.shiftLeftZeroExtend 13#8 1 = 26#9 := by with_implicit rfl
example : BitVec.extractLsb' 1 1 13#8 = 0#1 := by with_implicit rfl
example : BitVec.replicate 8 1#1 = 255#8 := by with_implicit rfl
example : BitVec.setWidth 4 13#8 = 13#4 := by with_implicit rfl
example : BitVec.zeroExtend 8 15#4 = 15#8 := by with_implicit rfl
example : BitVec.signExtend 8 15#4 = 255#8 := by with_implicit rfl
example : BitVec.allOnes 8 = 255#8 := by with_implicit rfl
example : BitVec.ofFin (Fin.mk 3 (show 3 < 2 ^ 8 by grind)) = 3#8 := by with_implicit rfl
example : BitVec.toFin 3#8 = Fin.mk 3 (show 3 < 2 ^ 8 by grind) := by with_implicit rfl

end BitVec

section Char

example : 'A'.toLower = 'a' := by with_implicit rfl
example : 'a'.toUpper = 'A' := by with_implicit rfl
example : 'A'.toNat = 65 := by with_implicit rfl
example : ' '.isWhitespace = true := by with_implicit rfl
example : 'A'.isUpper = true := by with_implicit rfl
example : 'a'.isLower = true := by with_implicit rfl
example : 'a'.isAlpha = true := by with_implicit rfl
example : '5'.isDigit = true := by with_implicit rfl
example : '5'.isAlphanum = true := by with_implicit rfl
example : toString 'A' = "A" := by with_implicit rfl
example : 'A'.val = 65 := by with_implicit rfl
example : ('A' == 'B') = false := by with_implicit rfl
example : ('A' != 'B') = true := by with_implicit rfl
example : Char.ofNat 65 = 'A' := by with_implicit rfl
example : Char.ofNatAux 65 (by decide) = 'A' := by with_implicit rfl
example : (default : Char) = 'A' := by with_implicit rfl

-- This is the `rfl` lemma `Char.toNat_val`.
example (c : Char) : c.val.toNat = c.toNat := by with_implicit rfl

end Char

section Fin

example : (2 : Fin 5).succ = 3 := by with_implicit rfl
example : (2 : Fin 5).rev = 2 := by with_implicit rfl
example : Fin.last 5 = 5 := by with_implicit rfl
example : (2 : Fin 5) + 3 = 0 := by with_implicit rfl
example : (2 : Fin 5) * 3 = 1 := by with_implicit rfl
example : (3 : Fin 5) - 1 = 2 := by with_implicit rfl
example : (4 : Fin 5) / 2 = 2 := by with_implicit rfl
example : (4 : Fin 5) % 3 = 1 := by with_implicit rfl
example : (3 : Fin 8) &&& 5 = 1 := by with_implicit rfl
example : (3 : Fin 8) ||| 5 = 7 := by with_implicit rfl
example : (3 : Fin 8) ^^^ 5 = 6 := by with_implicit rfl
example : (3 : Fin 8) <<< (1 : Fin 8) = 6 := by with_implicit rfl
example : (4 : Fin 8) >>> (1 : Fin 8) = 2 := by with_implicit rfl
example : ((3 : Fin 5) == 3) = true := by with_implicit rfl
example : ((3 : Fin 5) != 4) = true := by with_implicit rfl
example : (3 : Fin 5) = ⟨3, by decide⟩ := by with_implicit rfl
example : (Fin.mk 3 (by decide) : Fin 5) = 3 := by with_implicit rfl
example : Fin.ofNat 5 3 = (3 : Fin 5) := by with_implicit rfl
example : Fin.castSucc (3 : Fin 5) = 3 := by with_implicit rfl
example : Fin.castAdd 3 (2 : Fin 5) = 2 := by with_implicit rfl
example : Fin.addNat (2 : Fin 5) 3 = 5 := by with_implicit rfl
example : Fin.natAdd 3 (2 : Fin 5) = 5 := by with_implicit rfl
example : Fin.castLT (2 : Fin 5) (by decide) = (2 : Fin 3) := by with_implicit rfl
example : Fin.castLE (show 5 ≤ 8 by decide) (2 : Fin 5) = 2 := by with_implicit rfl
example : Fin.subNat 2 (5 : Fin 8) (by decide) = 3 := by with_implicit rfl
example : Fin.pred (3 : Fin 6) (by decide) = 2 := by with_implicit rfl

end Fin

section List

example : List.replicate 3 5 = [5, 5, 5] := by with_implicit rfl

end List

section String

example : "abc" ++ "def" = "abcdef" := by with_implicit rfl
example : String.ofList ['a', 'b', 'c'] = "abc" := by with_implicit rfl
example : "abc".toList = ['a', 'b', 'c'] := by with_implicit rfl
example : "ab".push 'c' = "abc" := by with_implicit rfl
example : String.singleton 'A' = "A" := by with_implicit rfl
example : "A" = String.singleton 'A' := by with_implicit rfl
example : ("A" == "B") = false := by with_implicit rfl
example : ("A" != "B") = true := by with_implicit rfl

end String

section Nat

example : 3 + 5 = 8 := by with_implicit rfl
example : 5 - 3 = 2 := by with_implicit rfl
example : 3 * 5 = 15 := by with_implicit rfl
example : 13 / 5 = 2 := by with_implicit rfl
example : 13 % 5 = 3 := by with_implicit rfl
example : 3 ^ 2 = 9 := by with_implicit rfl
example : 3 &&& 5 = 1 := by with_implicit rfl
example : 3 ||| 5 = 7 := by with_implicit rfl
example : 3 ^^^ 5 = 6 := by with_implicit rfl
example : 3 <<< 1 = 6 := by with_implicit rfl
example : 3 >>> 1 = 1 := by with_implicit rfl
example : Nat.gcd 10 15 = 5 := by with_implicit rfl
example : (13 == 12) = false := by with_implicit rfl
example : (13 != 12) = true := by with_implicit rfl

end Nat

section Int

example : -(-3) = (3 : Int) := by with_implicit rfl
example : 3 + 5 = (8 : Int) := by with_implicit rfl
example : 5 - 3 = (2 : Int) := by with_implicit rfl
example : 3 * 5 = (15 : Int) := by with_implicit rfl
example : 13 / 5 = (2 : Int) := by with_implicit rfl
example : Int.tdiv 13 5 = (2 : Int) := by with_implicit rfl
example : Int.fdiv 13 5 = (2 : Int) := by with_implicit rfl
example : Int.bdiv 13 5 = (3 : Int) := by with_implicit rfl
example : 13 % 5 = (3 : Int) := by with_implicit rfl
example : Int.tmod 13 5 = (3 : Int) := by with_implicit rfl
example : Int.fmod 13 5 = (3 : Int) := by with_implicit rfl
example : Int.bmod 13 5 = (-2 : Int) := by with_implicit rfl
example : 3 ^ 2 = (9 : Int) := by with_implicit rfl
example : ((13 : Int) == 12) = false := by with_implicit rfl
example : ((13 : Int) != 12) = true := by with_implicit rfl
example : Int.natAbs (-5) = 5 := by with_implicit rfl
example : Int.toNat (-5) = 0 := by with_implicit rfl
example : Int.negSucc 2 = -3 := by with_implicit rfl
example : Int.ofNat 3 = 3 := by with_implicit rfl
example : NatCast.natCast 3 = (3 : Int) := by with_implicit rfl
example : Nat.cast 3 = (3 : Int) := by with_implicit rfl

end Int

section SInt
/-
`Lean.Meta.Tactic.Simp.BuiltinSimprocs` defines dsimprocs for operations such as `toInt` reductions
arithmetic.
We need to make sure that these are `rfl` at implicit transparency.
-/
example : Int8.minValue.toInt = - 2 ^ 7 := by with_implicit rfl
example : Int16.minValue.toInt = - 2 ^ 15 := by with_implicit rfl
example : Int32.minValue.toInt = - 2 ^ 31 := by with_implicit rfl
example : Int64.minValue.toInt = - 2 ^ 63 := by with_implicit rfl

example : 3 * 5 = (15 : Int8) := by with_implicit rfl
example : 3 * 5 = (15 : Int16) := by with_implicit rfl
example : 3 * 5 = (15 : Int32) := by with_implicit rfl
example : 3 * 5 = (15 : Int64) := by with_implicit rfl

example : 3 + 5 = (8 : Int8) := by with_implicit rfl
example : 3 + 5 = (8 : Int16) := by with_implicit rfl
example : 3 + 5 = (8 : Int32) := by with_implicit rfl
example : 3 + 5 = (8 : Int64) := by with_implicit rfl

example : 3 - 5 = (-2 : Int8) := by with_implicit rfl
example : 3 - 5 = (-2 : Int16) := by with_implicit rfl
example : 3 - 5 = (-2 : Int32) := by with_implicit rfl
example : 3 - 5 = (-2 : Int64) := by with_implicit rfl

example : 13 / 5 = (2 : Int8) := by with_implicit rfl
example : 13 / 5 = (2 : Int16) := by with_implicit rfl
example : 13 / 5 = (2 : Int32) := by with_implicit rfl
example : 13 / 5 = (2 : Int64) := by with_implicit rfl

example : 13 % 5 = (3 : Int8) := by with_implicit rfl
example : 13 % 5 = (3 : Int16) := by with_implicit rfl
example : 13 % 5 = (3 : Int32) := by with_implicit rfl
example : 13 % 5 = (3 : Int64) := by with_implicit rfl

section
set_option warn.sorry false
example : (13 : Int8) = Int8.ofIntLE 13 sorry sorry := by with_implicit rfl
example : (13 : Int16) = Int16.ofIntLE 13 sorry sorry := by with_implicit rfl
example : (13 : Int32) = Int32.ofIntLE 13 sorry sorry := by with_implicit rfl
example : (13 : Int64) = Int64.ofIntLE 13 sorry sorry := by with_implicit rfl
end

example : (13 : Int8) = Int8.ofNat 13 := by with_implicit rfl
example : (13 : Int16) = Int16.ofNat 13 := by with_implicit rfl
example : (13 : Int32) = Int32.ofNat 13 := by with_implicit rfl
example : (13 : Int64) = Int64.ofNat 13 := by with_implicit rfl

example : (13 : Nat) = (13 : Int8).toNatClampNeg := by with_implicit rfl
example : (0 : Nat) = (-13 : Int8).toNatClampNeg := by with_implicit rfl
example : (13 : Nat) = (13 : Int16).toNatClampNeg := by with_implicit rfl
example : (0 : Nat) = (-13 : Int16).toNatClampNeg := by with_implicit rfl
example : (13 : Nat) = (13 : Int32).toNatClampNeg := by with_implicit rfl
example : (0 : Nat) = (-13 : Int32).toNatClampNeg := by with_implicit rfl
example : (13 : Nat) = (13 : Int64).toNatClampNeg := by with_implicit rfl
example : (0 : Nat) = (-13 : Int64).toNatClampNeg := by with_implicit rfl

example : (-13 : Int8) = Int8.ofInt (-13) := by with_implicit rfl
example : (-13 : Int16) = Int16.ofInt (-13) := by with_implicit rfl
example : (-13 : Int32) = Int32.ofInt (-13) := by with_implicit rfl
example : (-13 : Int64) = Int64.ofInt (-13) := by with_implicit rfl

example : (-13 : Int) = (-13 : Int8).toInt := by with_implicit rfl
example : (-13 : Int) = (-13 : Int16).toInt := by with_implicit rfl
example : (-13 : Int) = (-13 : Int32).toInt := by with_implicit rfl
example : (-13 : Int) = (-13 : Int64).toInt := by with_implicit rfl

end SInt

section UInt

example : 3 * 5 = (15 : UInt8) := by with_implicit rfl
example : 3 * 5 = (15 : UInt16) := by with_implicit rfl
example : 3 * 5 = (15 : UInt32) := by with_implicit rfl
example : 3 * 5 = (15 : UInt64) := by with_implicit rfl

example : 3 + 5 = (8 : UInt8) := by with_implicit rfl
example : 3 + 5 = (8 : UInt16) := by with_implicit rfl
example : 3 + 5 = (8 : UInt32) := by with_implicit rfl
example : 3 + 5 = (8 : UInt64) := by with_implicit rfl

example : 5 - 3 = (2 : UInt8) := by with_implicit rfl
example : 5 - 3 = (2 : UInt16) := by with_implicit rfl
example : 5 - 3 = (2 : UInt32) := by with_implicit rfl
example : 5 - 3 = (2 : UInt64) := by with_implicit rfl

example : 13 / 5 = (2 : UInt8) := by with_implicit rfl
example : 13 / 5 = (2 : UInt16) := by with_implicit rfl
example : 13 / 5 = (2 : UInt32) := by with_implicit rfl
example : 13 / 5 = (2 : UInt64) := by with_implicit rfl

example : 13 % 5 = (3 : UInt8) := by with_implicit rfl
example : 13 % 5 = (3 : UInt16) := by with_implicit rfl
example : 13 % 5 = (3 : UInt32) := by with_implicit rfl
example : 13 % 5 = (3 : UInt64) := by with_implicit rfl

example : (13 : UInt8) = UInt8.ofNat 13 := by with_implicit rfl
example : (13 : UInt16) = UInt16.ofNat 13 := by with_implicit rfl
example : (13 : UInt32) = UInt32.ofNat 13 := by with_implicit rfl
example : (13 : UInt64) = UInt64.ofNat 13 := by with_implicit rfl

example : (13 : Nat) = (13 : UInt8).toNat := by with_implicit rfl
example : (13 : Nat) = (13 : UInt16).toNat := by with_implicit rfl
example : (13 : Nat) = (13 : UInt32).toNat := by with_implicit rfl
example : (13 : Nat) = (13 : UInt64).toNat := by with_implicit rfl

example : ((13 : UInt8) == 12) = false := by with_implicit rfl
example : ((13 : UInt8) != 12) = true := by with_implicit rfl
example : ((13 : UInt16) == 12) = false := by with_implicit rfl
example : ((13 : UInt16) != 12) = true := by with_implicit rfl
example : ((13 : UInt32) == 12) = false := by with_implicit rfl
example : ((13 : UInt32) != 12) = true := by with_implicit rfl
example : ((13 : UInt64) == 12) = false := by with_implicit rfl
example : ((13 : UInt64) != 12) = true := by with_implicit rfl

section
set_option warn.sorry false
example : UInt8.ofNatLT 13 sorry = 13 := by with_implicit rfl
example : UInt16.ofNatLT 13 sorry = 13 := by with_implicit rfl
example : UInt32.ofNatLT 13 sorry = 13 := by with_implicit rfl
example : UInt64.ofNatLT 13 sorry = 13 := by with_implicit rfl
end

example : UInt8.ofNat 13 = 13 := by with_implicit rfl
example : UInt16.ofNat 13 = 13 := by with_implicit rfl
example : UInt32.ofNat 13 = 13 := by with_implicit rfl
example : UInt64.ofNat 13 = 13 := by with_implicit rfl

example : UInt8.toNat 13 = 13 := by with_implicit rfl
example : UInt16.toNat 13 = 13 := by with_implicit rfl
example : UInt32.toNat 13 = 13 := by with_implicit rfl
example : UInt64.toNat 13 = 13 := by with_implicit rfl

end UInt

theorem toLower_eq_of_not_isUpper {c : Char} (h : ¬ c.isUpper) : c.toLower = c := by
  -- squashed: simp_all [isUpper, UInt32.le_iff_toNat_le, toLower]
  simp_all only [Char.isUpper, ↓Char.isValue, Char.reduceVal, ge_iff_le, UInt32.le_iff_toNat_le,
    UInt32.reduceToNat, Char.toNat_val, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, not_and,
    Nat.not_le, Char.toLower, UInt32.reduceSub, dite_eq_right_iff]
  omega
