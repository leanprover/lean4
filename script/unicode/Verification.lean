/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Init.Data.Char.UnicodeSkipList
import Init.Data.Char.Tables
import Unicode.Reference
import Unicode.Parse

open System IO FilePath Process FS Std Char.UnicodeSkipList

def compareTables (ucd : Array UnicodeData) (property : UnicodeData → Bool) : IO Bool := do
  let mut failed := false
  let table := numericTable
  let referenceTable := referenceTable ucd property
  for i in [:1114112] do
    let c := Char.ofNat i
    let ref := referenceSearch referenceTable c
    let candidate := search table c
    if ref ≠ candidate then
      failed := true
      println s!"Discrepancy: character {c} with decimal code {c.toNat} is {ref} in the reference and {candidate} in the skiplist"
  return failed

def main : IO Unit := do
  let workingDir : FilePath ← currentDir
  let dataDir : FilePath := join workingDir (System.mkFilePath ["Data"])
  unless ← dataDir.pathExists do
    createDir "Data"
  for dataset in unicodeDatasets do
    let f : FilePath := System.mkFilePath ["Data",dataset]
    discard <| download (unicodeUrl ++ dataset) f

  let f : FilePath := System.mkFilePath ["Data", "UnicodeData.txt"]
  let ucd ← loadUnicodeData f
  match ucd with
  | Except.ok ucd =>
      let property := fun ucdc : UnicodeData => if let .Number _ := ucdc.gc then true else false
      let failed ← compareTables ucd property
      if failed then
        IO.Process.exit 1
      else
        IO.Process.exit 0
  | Except.error msg =>
      println msg
      IO.Process.exit 1
