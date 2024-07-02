/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Init.Data.Char.UnicodeSkipList
import Unicode.UnicodeSkipList
import Unicode.Unicode
import Unicode.FetchDatabase

open System IO FilePath Process FS Std Char.UnicodeSkipList

def main : IO Unit := do
  let workingDir : FilePath ← currentDir
  let dataDir : FilePath := join workingDir (System.mkFilePath ["Data"])
  unless ← dataDir.pathExists do
    createDir "Data"
  for dataset in unicodeDatasets do
    let f : FilePath := System.mkFilePath ["Data", dataset]
    discard <| download (unicodeUrl ++ dataset) f

  let f : FilePath := System.mkFilePath ["Data", "UnicodeData.txt"]
  let ucd ← loadUnicodeData f
  match ucd with
  | Except.ok ucd =>
      println s! "UCD size: {ucd.size}"
      let summary := summarizeUnicodeData ucd
      printSummary summary
      let property := fun ucdc : UnicodeData => if let .Number _ := ucdc.gc then true else false
      let table := calculateTable ucd property
      writeUnicodeVersion
      writeTable "numeric" table
  | Except.error msg =>
    println msg
    IO.Process.exit 1
