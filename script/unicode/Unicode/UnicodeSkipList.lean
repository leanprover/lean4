/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Init.Data.Char.UnicodeSkipList
import Unicode.Unicode
import Unicode.Parse
import Init.Data.Char.Basic

open Std System IO FilePath FS

namespace Char.UnicodeSkipList

/-
The following code creates the unicode skip list data structure for
a given property. To understand it at a high-level, we provide an
explanation in Init/Data/Char/UnicodeSkipList.lean
-/

/-
Break down the sequence of codepoints into a sequence of ranges,
alternating between ranges that satisfy the property and ranges that
do not.
-/
def explicitRanges (ucd : List UnicodeData) (property : UnicodeData → Bool) : List Range := Id.run do
  let mut rangeOpt : Option Range := none
  let mut ranges := []
  for datapoint in ucd do
    let code := datapoint.codepoint
    let prop := property datapoint
    match rangeOpt, prop with
    | some r, true =>
      if r.stop + 1 = code then
        -- Extend the range
        rangeOpt := some { r with stop := code }
      else
        -- Hidden gap
        let completedRange : Range := { start := r.start , stop := r.stop + 1 }
        let newRange : Range := { start := code , stop := code }
        rangeOpt := some newRange
        ranges := completedRange :: ranges
    | some r, false =>
      -- Close the range
      -- Cannot use code for range end as their may be a jump in codepoints
      let completedRange : Range := { start := r.start , stop := r.stop + 1 }
      rangeOpt := none
      ranges := completedRange :: ranges
    | none, true =>
      -- Open a range
      let newRange : Range := { start := code , stop := code }
      rangeOpt := some newRange
    | none, false => ()

  return ranges

/-
Turn the list or ranges into a gap encoding.
-/
def mergeRanges (ranges : List Range) : List Nat := Id.run do
  let flat := ranges.foldl (fun acc => fun range => range.start :: range.stop :: acc) []
  let mut prev := 0
  let mut gaps := []
  for bound in flat do
    gaps := (bound - prev) :: gaps
    prev := bound
  gaps := (0 :: gaps).reverse
  return gaps

/-
Ranges with a length that cannot fit in 8 bits are encoded as 0.
-/
def offsets (gaps : List Nat) : Array UInt8 :=
  (gaps.map (fun gap => if gap ≥ 256 then 0 else gap.toUInt8)).toArray

/-
Compute the list of indices into the offset array, pointing to the
different runs.
-/
def indices (gaps : List Nat) : List Nat := Id.run do
  let mut index := 0
  let mut indices := [0]
  for gap in gaps do
    index := index + 1
    if gap ≥ 256 then
      indices := index * 2^21 :: indices
  return indices.reverse

/-
Computer the list of codepoint that mark the beginning of a run
in the original unicode data.
-/
def prefixSums (gaps : List Nat) : List Nat := Id.run do
  let mut prefixSum := 0
  let mut prefixSums := []
  for gap in gaps do
    prefixSum := prefixSum + gap
    if gap ≥ 256 then
      prefixSums := prefixSum :: prefixSums
  return prefixSums.reverse

def largeOffsetEncoding (indices prefixSums : List Nat) : Array UInt32 :=
  let prefixSums := prefixSums ++ [1114112]
  ((indices.zip prefixSums).map (fun (idx,pf) => (idx + pf).toUInt32)).toArray

def calculateTable (ucd : List UnicodeData) (property : UnicodeData → Bool) : UnicodePropertyTable :=
  let ranges := (explicitRanges ucd property)
  let gaps := mergeRanges ranges
  let offsets := offsets gaps
  let indices := indices gaps
  let prefixSums := prefixSums gaps
  let runs := largeOffsetEncoding indices prefixSums
  { runs, offsets }

def writeTable (property : String) (table : UnicodePropertyTable) : IO Unit := do
  let workingDir : FilePath ← currentDir
  let f : FilePath := join workingDir <| System.mkFilePath ["..","..","src","Init","Data","Char","Tables.lean"]
  let mut content := ""
  content := content ++ "/-\n"
  content := content ++ "Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.\n"
  content := content ++ "Released under Apache 2.0 license as described in the file LICENSE.\n"
  content := content ++ "Authors: Jean-Baptiste Tristan\n"
  content := content ++ "-/\n"
  content := content ++ "-- DO NOT EDIT: file generated using the scripts/unicode tool\n"
  content := content ++ "prelude\n"
  content := content ++ "import Init.Data.Char.UnicodeSkipList\n"
  content := content ++ "import Init.Data.Array.BasicAux\n"
  content := content ++ "\n"
  content := content ++ "namespace Char.UnicodeSkipList\n"
  content := content ++ s!"instance {property}Table : UnicodePropertyTable where\n"
  content := content ++ "  runs := #[\n"
  content := content ++ "    " ++ (reprStr (table.runs.get! 0))
  for i in [1:(table.runs.size)] do
    content := content ++ ", " ++ (reprStr (table.runs.get! i))
    if i % 10 = 0 then
      content := content ++ "\n    "
  content := content ++ "  ]\n"
  content := content ++ "  offsets := #[\n"
  content := content ++ "    " ++ (reprStr (table.offsets.get! 0))
  for i in [1:(table.offsets.size)] do
    content := content ++ ", " ++ (reprStr (table.offsets.get! i))
    if i % 10 = 0 then
      content := content ++ "\n    "
  content := content ++ "  ]\n"
  content := content ++ "\nend Char.UnicodeSkipList\n"
  writeFile f content

end Char.UnicodeSkipList
