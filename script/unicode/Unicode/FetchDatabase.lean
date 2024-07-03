/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

open System IO FilePath Process FS Std

def major : Nat := 15
def minor : Nat := 1
def update : Nat := 0

def unicodeUrl : String :=
  s!"https://www.unicode.org/Public/{major}.{minor}.{update}/ucd/"

def unicodeDatasets : List String := ["UnicodeData.txt"]

def download  (url : String) (file : FilePath) : IO Output := do
  if (¬ (← file.pathExists)) then
    output { cmd := "curl", args := #["-s", "-S", "-f", "-o", file.toString, "-L", url] }
  else pure { exitCode := 0, stdout := "", stderr := "" }

def writeUnicodeVersion : IO Unit := do
  let workingDir : FilePath ← currentDir
  let f : FilePath := join workingDir <| System.mkFilePath ["..", "..", "src", "Init", "Data", "Char", "UnicodeVersion.lean"]
  let mut content := ""
  content := content ++ "/-\n"
  content := content ++ "Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.\n"
  content := content ++ "Released under Apache 2.0 license as described in the file LICENSE.\n"
  content := content ++ "Authors: Jean-Baptiste Tristan\n"
  content := content ++ "-/\n"
  content := content ++ "-- DO NOT EDIT: file generated using the scripts/unicode tool\n"
  content := content ++ "prelude\n"
  content := content ++ "import Init.Data.Nat.Basic\n"
  content := content ++ "\n"
  content := content ++ "namespace Char\n\n"
  content := content ++ "/--\n"
  content := content ++ "The `unicodeVersion` definition gives Lean's current version of Unicode in format (major,minor,update). \n
                         New versions of Unicode are released regularly and subsequently all methods \n
                         in the standard library depending on Unicode are updated. Therefore the behavior \n
                          of some `Char` and `String` methods and the value of this constant changes \n
                          over time. *This is not considered to be a breaking change.*"
  content := content ++ "\n-/\n"
  content := content ++ s!"def unicodeVersion : Nat × Nat × Nat := ({major},{minor},{update})\n"
  content := content ++ "\nend Char\n"
  writeFile f content
