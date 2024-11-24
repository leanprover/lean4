/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.System.IO
import Std.Tactic.BVDecide.LRAT.Actions
import Std.Internal.Parsec

/-!
This module implements parsers and serializers for both the binary and non-binary LRAT format.
-/

namespace Std.Tactic.BVDecide

open Std.Sat
open Std.Tactic.BVDecide.LRAT (IntAction)

namespace LRAT
namespace Parser

private def getPivot (clause : Array Int) : Literal Nat :=
  let pivotInt := clause[0]!
  if pivotInt > 0 then
    (pivotInt.natAbs, true)
  else
    (pivotInt.natAbs, false)


open Std.Internal.Parsec
open Std.Internal.Parsec.ByteArray

namespace Text

@[inline]
def skipNewline : Parser Unit := do
  skipByteChar '\n' <|> skipString "\r\n"

/-
This implements a (corrected) version of the grammar presented in:
https://www.cs.cmu.edu/~mheule/publications/lrat.pdf

The production rules ⟨clause⟩ and ⟨rat⟩ in Fig. 3. would mandate to put two 0 after the new
clause that the current proof step is producing, that is not the case.
-/

@[inline]
def parsePos : Parser Nat := do
  let ident ← digits
  if ident == 0 then
    fail "id was 0"
  else
    return ident

@[inline]
def parseNeg : Parser Int := do
  skipByteChar '-'
  let nat ← parsePos
  return -nat

@[inline]
def parseId : Parser Nat := parsePos

@[inline]
def parseZero : Parser Unit := skipByteChar '0'

def parseIdList : Parser (Array Nat) := do
  many idWs
where
  @[inline]
  idWs : Parser Nat := do
    let ident ← attempt parseId
    skipByteChar ' '
    return ident

def parseDelete : Parser IntAction := do
  skipByteChar 'd'
  skipByteChar ' '
  let idList ← parseIdList
  parseZero
  return .del idList

@[inline]
def parseLit : Parser Int := do
  if (← peek!) == '-'.toUInt8 then
    parseNeg
  else
    Int.ofNat <$> parsePos

def parseClause : Parser (Array Int) := do
  let lits ← many litWs
  parseZero
  return lits
where
  @[inline]
  litWs : Parser Int := do
    let lit ← attempt parseLit
    skipByteChar ' '
    return lit

def parseRes : Parser (Nat × Array Nat) := do
  let lhs ← parseNeg
  skipByteChar ' '
  let idents ← parseIdList
  return (lhs.natAbs, idents)

def parseRat (ident : Nat) : Parser IntAction := do
  let clause ← parseClause
  skipByteChar ' '
  let rupHints ← parseIdList
  let ratHints ← many (attempt parseRes)
  parseZero
  match clause.size, ratHints.size with
  | 0, 0 => return .addEmpty ident rupHints
  | 0, _ => fail "There cannot be any ratHints for adding the empty clause"
  | _, 0 => return .addRup ident clause rupHints
  | _, _ => return .addRat ident clause (getPivot clause) rupHints ratHints

def parseAction : Parser IntAction := do
  let ident ← parseId
  skipByteChar ' '
  if (← peek!) == 'd'.toUInt8 then
    parseDelete
  else
    parseRat ident

partial def parseActions : Parser (Array IntAction) :=
  go #[]
where
  go (actions : Array IntAction) : Parser (Array IntAction) := do
    if (← peek!) == 'c'.toUInt8 then
      let _ ← many (satisfy (fun c => c != '\n'.toUInt8 && c != '\r'.toUInt8))
      skipNewline
      if ← isEof then
        return actions
      else
        go actions
    else
      let action ← parseAction
      skipNewline
      let actions := actions.push action
      if ← isEof then
        return actions
      else
        go actions

end Text

namespace Binary

@[inline]
def parseZero : Parser Unit := skipByte 0

-- see: https://github.com/marijnheule/drat-trim?tab=readme-ov-file#binary-drat-format
-- see: https://github.com/arminbiere/lrat-trim/blob/80f22c57fb2d74cb72210f5b334a1ffe2160a628/lrat-trim.c#L1579-L1595
partial def parseLit : Parser Int := do
  go 0 0
where
  go (uidx : UInt64) (shift : UInt64) : Parser Int := do
    let uch ← any
    if shift == 28 && ((uch &&& ~~~15) != 0) then
      fail "Excessive literal"
    else if uch == 0 then
      fail "Invalid zero byte in literal"
    else
      let uidx := uidx ||| ((uch &&& 127).toUInt64 <<< shift)
      if uch &&& 128 == 0 then
        let idx := uidx >>> 1
        if (1 &&& uidx) != 0 then
          return (-(idx).toNat : Int)
        else
          return (idx.toNat : Int)
      else
        go uidx (shift + 7)

@[inline]
def parseNeg : Parser Nat := do
  let lit ← parseLit
  if lit < 0 then
    return lit.natAbs
  else
    fail "parsed non negative lit where negative was expected"

@[inline]
def parsePos : Parser Nat := do
  let lit ← parseLit
  if lit > 0 then
    return lit.natAbs
  else
    fail "parsed non positive lit where positive was expected"

@[inline]
def parseId : Parser Nat := parsePos

@[specialize]
partial def manyTillZero (parser : Parser α) : Parser (Array α) :=
  go #[]
where
  @[specialize]
  go (acc : Array α) : Parser (Array α) := do
    if (← peek!) == 0 then
      return acc
    else
      let elem ← parser
      go <| acc.push elem

@[specialize]
partial def manyTillNegOrZero (parser : Parser α) : Parser (Array α) :=
  go #[]
where
  @[specialize]
  go (acc : Array α) : Parser (Array α) := do
    let byte ← peek!
    if (1 &&& byte != 0) || byte == 0 then
      return acc
    else
      let elem ← parser
      go <| acc.push elem

@[inline]
def parseIdList : Parser (Array Nat) :=
  manyTillNegOrZero parseId

@[inline]
def parseClause : Parser (Array Int) := do
  manyTillZero parseLit

def parseRes : Parser (Nat × Array Nat) := do
  let lhs ← parseNeg
  let idents ← parseIdList
  return (lhs, idents)

@[inline]
def parseRatHints : Parser (Array (Nat × Array Nat)) := do
  manyTillZero parseRes

def parseAction : Parser IntAction := do
  let discr ← any
  if discr == 'a'.toUInt8 then
    parseAdd
  else if discr == 'd'.toUInt8 then
    parseDelete
  else
    fail s!"Expected a or d got: {discr}"
where
  parseAdd : Parser IntAction := do
    let ident ← parseId
    let clause ← parseClause
    parseZero
    let rupHints ← parseIdList
    let ratHints ← parseRatHints
    parseZero
    match clause.size, ratHints.size with
    | 0, 0 => return .addEmpty ident rupHints
    | 0, _ => fail "There cannot be any ratHints for adding the empty clause"
    | _, 0 => return .addRup ident clause rupHints
    | _, _ => return .addRat ident clause (getPivot clause) rupHints ratHints

  parseDelete : Parser IntAction := do
    let idList ← parseIdList
    parseZero
    return .del idList

def parseActions : Parser (Array IntAction) := do
  let actions ← many parseAction
  eof
  return actions

end Binary

/--
Based on the first byte parses the input either as a binary or non-binary LRAT.
-/
def parseActions : Parser (Array IntAction) := do
  let byte ← peek!
  if byte == 'a'.toUInt8 || byte == 'd'.toUInt8 then
    Binary.parseActions
  else
    Text.parseActions

end Parser

/--
Read and parse an LRAT proof from `path`. `path` may contain either the binary or the non-binary
LRAT format.
-/
def loadLRATProof (path : System.FilePath) : IO (Array IntAction) := do
  let proof ← IO.FS.readBinFile path
  match Parser.parseActions.run proof with
  | .ok actions => return actions
  | .error err => throw <| .userError err

/--
Parse `proof` as an LRAT proof. `proof` may contain either the binary or the non-binary LRAT format.
-/
def parseLRATProof (proof : ByteArray) : Except String (Array IntAction) :=
  Parser.parseActions.run proof

/--
Serialize `proof` into the non-binary LRAT format as a `String`.
-/
def lratProofToString (proof : Array IntAction) : String :=
  proof.foldl (init := "") (· ++ serialize · ++ "\n")
where
  serialize (a : IntAction) : String :=
    match a with
    | .addEmpty id hints =>
      s!"{id} 0 {serializeIdList hints}0"
    | .addRup id c hints =>
      s!"{id} {serializeClause c}0 {serializeIdList hints}0"
    | .addRat id c _ rupHints ratHints =>
      s!"{id} {serializeClause c}0 {serializeIdList rupHints}{serializeRatHints ratHints}0"
    | .del ids =>
      -- Note: 1 is not the actual step id but step ids don't matter for deletes
      s!"1 d {serializeIdList ids}0"

  serializeIdList (ids : Array Nat) : String :=
    ids.foldl (init := "") (· ++ s!"{·} ")

  serializeClause (clause : Array Int) : String :=
    clause.foldl (init := "") (· ++ s!"{·} ")

  serializeRatHint (hint : Nat × Array Nat) : String :=
    s!"-{hint.fst} {serializeIdList hint.snd}"

  serializeRatHints (hints : Array (Nat × Array Nat)) : String :=
    hints.foldl (init := "") (· ++ serializeRatHint ·)

/--
Serialize `proof` into the binary LRAT format as a `ByteArray`.
-/
partial def lratProofToBinary (proof : Array IntAction) : ByteArray :=
  -- we will definitely need at least 4 bytes per add step and almost exclusively produce add.
  go 0 (ByteArray.mkEmpty (4 * proof.size))
where
  go (idx : Nat) (acc : ByteArray) : ByteArray :=
    if h : idx < proof.size then
      let acc :=
        match proof[idx] with
        | .addEmpty id hints =>
          let acc := startAdd acc
          let acc := addNat acc id
          let acc := zeroByte acc
          let acc := hints.foldl (init := acc) addNat
          let acc := zeroByte acc
          acc
        | .addRup id c hints =>
          let acc := startAdd acc
          let acc := addNat acc id
          let acc := c.foldl (init := acc) addInt
          let acc := zeroByte acc
          let acc := hints.foldl (init := acc) addNat
          let acc := zeroByte acc
          acc
        | .addRat id c _ rupHints ratHints =>
          let acc := startAdd acc
          let acc := addNat acc id
          let acc := c.foldl (init := acc) addInt
          let acc := zeroByte acc
          let acc := rupHints.foldl (init := acc) addNat
          let ratHintFolder acc hint :=
            let acc := addInt acc (-hint.fst)
            let acc := hint.snd.foldl (init := acc) addNat
            acc
          let acc := ratHints.foldl (init := acc) ratHintFolder
          let acc := zeroByte acc
          acc
        | .del ids =>
          let acc := startDelete acc
          let acc := ids.foldl (init := acc) addNat
          let acc := zeroByte acc
          acc
      go (idx + 1) acc
    else
      acc

  addInt (acc : ByteArray) (lit : Int) : ByteArray :=
    let mapped :=
      if lit > 0 then
        2 * lit.natAbs
      else
        2 * lit.natAbs + 1
    assert! mapped ≤ (2^64 - 1) -- our parser "only" supports 64 bit literals
    let mapped := mapped.toUInt64
    variableLengthEncode acc mapped

  variableLengthEncode (acc : ByteArray) (lit : UInt64) : ByteArray :=
    -- once the literal is 0 we don't need to add another byte.
    if lit == 0 then
      acc
    else
      let chunk :=
        if lit > 127 then
          (lit.toUInt8 &&& 127) ||| 128
        else
          lit.toUInt8 &&& 127
      let acc := acc.push chunk
      variableLengthEncode acc (lit >>> 7)

  @[inline]
  startAdd (acc : ByteArray) : ByteArray := acc.push 'a'.toUInt8

  @[inline]
  startDelete (acc : ByteArray) : ByteArray := acc.push 'd'.toUInt8

  @[inline]
  zeroByte (acc : ByteArray) : ByteArray := acc.push 0

  @[inline]
  addNat (acc : ByteArray) (n : Nat) : ByteArray := addInt acc n

/--
Dump `proof` into `path`, either in the binary or non-binary LRAT format, depending on `binaryProofs`.
-/
def dumpLRATProof (path : System.FilePath) (proof : Array IntAction) (binaryProofs : Bool) :
    IO Unit := do
  let out :=
    if binaryProofs then
      lratProofToBinary proof
    else
      lratProofToString proof |>.toUTF8
  IO.FS.writeBinFile path out

end LRAT

end Std.Tactic.BVDecide
