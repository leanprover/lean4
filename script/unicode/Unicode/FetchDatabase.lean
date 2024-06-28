/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

open System IO FilePath Process FS Std

def unicodeVersion : Nat × Nat × Nat := (15,1,0)

def unicodeUrl : String :=
  let major : Nat := unicodeVersion.1
  let minor : Nat := unicodeVersion.2.1
  let update : Nat := unicodeVersion.2.2
  s!"https://www.unicode.org/Public/{major}.{minor}.{update}/ucd/"

def unicodeDatasets : List String := ["UnicodeData.txt"]

def download  (url : String) (file : FilePath) : IO Output := do
  if (¬ (← file.pathExists)) then
    output { cmd := "curl", args := #["-s", "-S", "-f", "-o", file.toString, "-L", url] }
  else pure { exitCode := 0, stdout := "", stderr := "" }
