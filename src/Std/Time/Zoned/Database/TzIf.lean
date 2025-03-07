/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.Data.Range
import Std.Internal.Parsec
import Std.Internal.Parsec.ByteArray

-- Based on: https://www.rfc-editor.org/rfc/rfc8536.html

namespace Std
namespace Time
namespace TimeZone
namespace TZif
open Std.Internal.Parsec Std.Internal.Parsec.ByteArray

set_option linter.all true

private abbrev Int32 := Int

private abbrev Int64 := Int

/--
Represents the header of a TZif file, containing metadata about the file's structure.
-/
structure Header where

  /--
  The version of the TZif file format.
  -/
  version : UInt8

  /--
  The count of UT local indicators in the file.
  -/
  isutcnt : UInt32

  /--
  The count of standard/wall indicators in the file.
  -/
  isstdcnt : UInt32

  /--
  The number of leap second records.
  -/
  leapcnt : UInt32

  /--
  The number of transition times in the file.
  -/
  timecnt : UInt32

  /--
  The number of local time types in the file.
  -/
  typecnt : UInt32

  /--
  The total number of characters used in abbreviations.
  -/
  charcnt : UInt32
  deriving Repr, Inhabited

/--
Represents the local time type information, including offset and daylight saving details.
-/
structure LocalTimeType where

  /--
  The GMT offset in seconds for this local time type.
  -/
  gmtOffset : Int32

  /--
  Indicates if this local time type observes daylight saving time.
  -/
  isDst : Bool

  /--
  The index into the abbreviation string table for this time type.
  -/
  abbreviationIndex : UInt8
  deriving Repr, Inhabited

/--
Represents a leap second record, including the transition time and the correction applied.
-/
structure LeapSecond where

  /--
  The transition time of the leap second event.
  -/
  transitionTime : Int64

  /--
  The correction applied during the leap second event in seconds.
  -/
  correction : Int64
  deriving Repr, Inhabited

/--
Represents version 1 of the TZif format.
-/
structure TZifV1 where

  /--
  The header information of the TZif file.
  -/
  header : Header

  /--
  The array of transition times in seconds since the epoch.
  -/
  transitionTimes : Array Int32

  /--
  The array of local time type indices corresponding to each transition time.
  -/
  transitionIndices : Array UInt8

  /--
  The array of local time type structures.
  -/
  localTimeTypes : Array LocalTimeType

  /--
  The array of abbreviation strings used by local time types.
  -/
  abbreviations : Array String

  /--
  The array of leap second records.
  -/
  leapSeconds : Array LeapSecond

  /--
  The array indicating whether each transition time uses wall clock time or standard time.
  -/
  stdWallIndicators : Array Bool

  /--
  The array indicating whether each transition time uses universal time or local time.
  -/
  utLocalIndicators : Array Bool
  deriving Repr, Inhabited

/--
Represents version 2 of the TZif format, extending TZifV1 with an optional footer.
-/
structure TZifV2 extends TZifV1 where

  /--
  An optional footer for additional metadata in version 2.
  -/
  footer : Option String
  deriving Repr, Inhabited

/--
Represents a TZif file, which can be either version 1 or version 2.
-/
structure TZif where

  /--
  The data for version 1 of the TZif file.
  -/
  v1 : TZifV1

  /--
  Optionally, the data for version 2 of the TZif file.
  -/
  v2 : Option TZifV2
  deriving Repr, Inhabited

private def toUInt32 (bs : ByteArray) : UInt32 :=
  assert! bs.size == 4
  (bs.get! 0).toUInt32 <<< 0x18 |||
  (bs.get! 1).toUInt32 <<< 0x10 |||
  (bs.get! 2).toUInt32 <<< 0x8  |||
  (bs.get! 3).toUInt32

private def toInt32 (bs : ByteArray) : Int32 :=
  let n := toUInt32 bs |>.toNat
  if n < (1 <<< 31)
    then Int.ofNat n
    else Int.negOfNat (UInt32.size - n)

private def toInt64 (bs : ByteArray) : Int64 :=
  let n := ByteArray.toUInt64BE! bs |>.toNat
  if n < (1 <<< 63)
    then Int.ofNat n
    else Int.negOfNat (UInt64.size - n)

private def manyN (n : Nat) (p : Parser α) : Parser (Array α) := do
  let mut result := #[]
  for _ in [0:n] do
    let x ← p
    result := result.push x
  return result

private def pu64 : Parser UInt64 := ByteArray.toUInt64LE! <$> take 8
private def pi64 : Parser Int64 := toInt64 <$> take 8
private def pu32 : Parser UInt32 := toUInt32 <$> take 4
private def pi32 : Parser Int32 := toInt32 <$> take 4
private def pu8 : Parser UInt8 := any
private def pbool : Parser Bool := (· != 0) <$> pu8

private def parseHeader : Parser Header :=
  Header.mk
    <$> (pstring "TZif" *> pu8)
    <*> (take 15 *> pu32)
    <*> pu32
    <*> pu32
    <*> pu32
    <*> pu32
    <*> pu32

private def parseLocalTimeType : Parser LocalTimeType :=
  LocalTimeType.mk
    <$> pi32
    <*> pbool
    <*> pu8

private def parseLeapSecond (p : Parser Int) : Parser LeapSecond :=
  LeapSecond.mk
    <$> p
    <*> pi32

private def parseTransitionTimes (size : Parser Int32) (n : UInt32) : Parser (Array Int32) :=
  manyN (n.toNat) size

private def parseTransitionIndices (n : UInt32) : Parser (Array UInt8) :=
  manyN (n.toNat) pu8

private def parseLocalTimeTypes (n : UInt32) : Parser (Array LocalTimeType) :=
  manyN (n.toNat) parseLocalTimeType

private def parseAbbreviations (times : Array LocalTimeType) (n : UInt32) : Parser (Array String) := do
  let mut strings := #[]
  let mut current := ""
  let mut chars ← manyN n.toNat pu8

  for time in times do
    for indx in [time.abbreviationIndex.toNat:n.toNat] do
      let char := chars[indx]!
      if char = 0 then
        strings := strings.push current
        current := ""
        break
      else
        current := current.push (Char.ofUInt8 char)

  return strings

private def parseLeapSeconds (size : Parser Int) (n : UInt32) : Parser (Array LeapSecond) :=
  manyN (n.toNat) (parseLeapSecond size)

private def parseIndicators (n : UInt32) : Parser (Array Bool) :=
  manyN (n.toNat) pbool

private def parseTZifV1 : Parser TZifV1 := do
  let header ← parseHeader

  let transitionTimes ← parseTransitionTimes pi32 header.timecnt
  let transitionIndices ← parseTransitionIndices header.timecnt
  let localTimeTypes ← parseLocalTimeTypes header.typecnt
  let abbreviations ← parseAbbreviations localTimeTypes header.charcnt
  let leapSeconds ← parseLeapSeconds pi32 header.leapcnt
  let stdWallIndicators ← parseIndicators header.isstdcnt
  let utLocalIndicators ← parseIndicators header.isutcnt

  return {
      header
      transitionTimes
      transitionIndices
      localTimeTypes
      abbreviations
      leapSeconds
      stdWallIndicators
      utLocalIndicators
  }

private def parseFooter : Parser (Option String) := do
  let char ← pu8

  if char = 0x0A then pure () else return none

  let tzString ← many (satisfy (· ≠ 0x0A))
  let mut str := ""

  for byte in tzString do
    str := str.push (Char.ofUInt8 byte)

  return str

private def parseTZifV2 : Parser (Option TZifV2) := optional do
  let header ← parseHeader

  let transitionTimes ← parseTransitionTimes pi64 header.timecnt
  let transitionIndices ← parseTransitionIndices header.timecnt
  let localTimeTypes ← parseLocalTimeTypes header.typecnt
  let abbreviations ← parseAbbreviations localTimeTypes header.charcnt
  let leapSeconds ← parseLeapSeconds pi64 header.leapcnt
  let stdWallIndicators ← parseIndicators header.isstdcnt
  let utLocalIndicators ← parseIndicators header.isutcnt

  return {
      header
      transitionTimes
      transitionIndices
      localTimeTypes
      abbreviations
      leapSeconds
      stdWallIndicators
      utLocalIndicators
      footer := ← parseFooter
  }

/--
Parses a TZif file, which may be in either version 1 or version 2 format.
-/
def parse : Parser TZif := do
  let v1 ← parseTZifV1
  let v2 ← parseTZifV2
  return { v1, v2 }

end TZif
