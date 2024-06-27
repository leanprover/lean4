import UtgLean4.Init.Lookup
import UtgLean4.Init.Util
import UtgLean4.Tool.Unicode
import UtgLean4.Tool.Parse

open System IO FilePath Process FS Std

structure SummaryUCD where
  letterCount : Int := 0
  markCount : Int := 0
  numberCount : Int := 0
  punctuationCount : Int := 0
  symbolCount : Int := 0
  separatorCount : Int := 0
  otherCount : Int := 0
  deriving Repr, DecidableEq, Inhabited, Nonempty

def summarizeUnicodeData (ucd : List UnicodeData) : SummaryUCD := Id.run do
  let mut table : SummaryUCD := {}
  for entry in ucd do
    match entry.gc with
    | GeneralCategory.Letter _ => table := { table with letterCount := table.letterCount + 1 }
    | GeneralCategory.Mark _ => table := { table with markCount := table.markCount + 1 }
    | GeneralCategory.Number _ => table := { table with numberCount := table.numberCount + 1 }
    | GeneralCategory.Punctuation _ => table := { table with punctuationCount := table.punctuationCount + 1 }
    | GeneralCategory.Symbol _ => table := { table with symbolCount := table.symbolCount + 1 }
    | GeneralCategory.Separator _ => table := { table with separatorCount := table.separatorCount + 1 }
    | GeneralCategory.Other _ => table := { table with otherCount := table.otherCount + 1 }
  return table

def printSummary (sucd : SummaryUCD) : IO Unit := do
  println s!"Letter count: {sucd.letterCount}"
  println s!"Mark count: {sucd.markCount}"
  println s!"Number count: {sucd.numberCount}"
  println s!"Punctuation count: {sucd.punctuationCount}"
  println s!"Symbol count: {sucd.symbolCount}"
  println s!"Separator count: {sucd.separatorCount}"
  println s!"Other count: {sucd.otherCount}"

def printUnicodeData (ucd : List UnicodeData) : IO Unit := do
  for entry in ucd do
    println <| reprStr entry

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
        rangeOpt := some {r with stop := code}
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

def mergeRanges (ranges : List Range) : List Nat := Id.run do
  let flat := ranges.foldl (fun acc => fun range => range.start :: range.stop :: acc) []
  let mut prev := 0
  let mut gaps := []
  for bound in flat do
    gaps := (bound - prev) :: gaps
    prev := bound
  gaps := (0 :: gaps).reverse
  return gaps

def offsets (gaps : List Nat) : Array UInt8 :=
  (gaps.map (fun gap => if gap ≥ 256 then 0 else gap.toUInt8)).toArray

def indices (gaps : List Nat) : List Nat := Id.run do
  let mut index := 0
  let mut indices := [0]
  for gap in gaps do
    index := index + 1
    if gap ≥ 256 then
      indices := index * 2^21 :: indices
  return indices.reverse

def prefixSums (gaps : List Nat) : List Nat := Id.run do
  let mut prefixSum := 0
  let mut prefixSums := []
  for gap in gaps do
    prefixSum := prefixSum + gap
    if gap ≥ 256 then
      prefixSums := prefixSum :: prefixSums
  return prefixSums.reverse

def largeOffsetEncoding (indices prefixSums : List Nat) : Array UInt32 :=
  let prefixSums := prefixSums ++ [1114111 + 1]
  ((indices.zip prefixSums).map (fun (idx,pf) => (idx + pf).toUInt32)).toArray

def calculateTable (ucd : List UnicodeData) (property : UnicodeData → Bool) : UcdPropertyTable :=
  let ranges := (explicitRanges ucd property)
  let gaps := mergeRanges ranges
  let offsets := offsets gaps
  let indices := indices gaps
  let prefixSums := prefixSums gaps
  let runs := largeOffsetEncoding indices prefixSums
  { runs, offsets }

@[simp]
noncomputable def skiplist (ucd : List UnicodeData) (property : UnicodeData → Bool) (c : Char) :=
  let table := calculateTable ucd property
  search table c

def writeTable (property : String) (table : UcdPropertyTable) : IO Unit := do
  let workingDir : FilePath ← currentDir
  let f : FilePath := join workingDir <| System.mkFilePath ["UtgLean4","Init","Tables.lean"]
  let mut content := ""
  content := content ++ "import UtgLean4.Init.Lookup\n"
  content := content ++ "\n"
  content := content ++ s!"instance {property}Table : UcdPropertyTable where\n"
  content := content ++ "  runs := #[\n"
  content := content ++ "    " ++ (reprStr (table.runs.get! 0))
  for i in Range.mk 1 (table.runs.size) 1 do
    content := content ++ ", " ++ (reprStr (table.runs.get! i))
    if i % 10 = 0 then
      content := content ++ "\n    "
  content := content ++ "  ]\n"
  content := content ++ "  offsets := #[\n"
  content := content ++ "    " ++ (reprStr (table.offsets.get! 0))
  for i in Range.mk 1 (table.offsets.size) 1 do
    content := content ++ ", " ++ (reprStr (table.offsets.get! i))
    if i % 10 = 0 then
      content := content ++ "\n    "
  content := content ++ "  ]\n"
  writeFile f content

def main : IO Unit := do
  let workingDir : FilePath ← currentDir
  let dataDir : FilePath := join workingDir (System.mkFilePath ["Data"])
  if (¬ (← dataDir.pathExists)) then
    createDir "Data"
  for dataset in unicodeDatasets do
    let f : FilePath := System.mkFilePath ["Data",dataset]
    let _ ← download (unicodeUrl ++ dataset) f

  let f : FilePath := System.mkFilePath ["Data","UnicodeData.txt"]
  let ucd₁ : ExceptT String IO (List UnicodeData) := loadUnicodeData f
  let ucd₄ : Except String (List UnicodeData) ← ucd₁
  match ucd₄ with
  | Except.ok ucd₅ =>
      println s! "UCD size: {ucd₅.length}"
      let summary := summarizeUnicodeData ucd₅
      printSummary summary
      let property := (fun ucdc : UnicodeData => if let .Number _ := ucdc.gc then true else false)
      let table := calculateTable ucd₅ property
      writeTable "numeric" table
  | Except.error msg => println msg
