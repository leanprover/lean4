import Init.Data.Char.UnicodeSkipList
import Init.Data.Char.Tables
import Unicode.Reference
import Unicode.Parse

open System IO FilePath Process FS Std

def compareTables (ucd : List UnicodeData) (property : UnicodeData → Bool) : IO Unit := do
  let time ← monoMsNow
  let mut failed := false
  let table := numericTable
  let referenceTable := referenceTable ucd property
  for i in Range.mk 0 1114112 1 do
    let c := Char.ofNat i
    let ref := referenceSearch referenceTable c
    let candidate := search table c
    if ref ≠ candidate then
      failed := true
      println s!"{c.toNat} {c} {ref} {candidate}"
  let msg := if failed then "failed" else "succeeded"
  println s!"Verification {msg} in {((← monoMsNow) - time).toFloat / 1000} seconds"

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
      let property := (fun ucdc : UnicodeData => if let .Number _ := ucdc.gc then true else false)
      compareTables ucd₅ property
  | Except.error msg => println msg
