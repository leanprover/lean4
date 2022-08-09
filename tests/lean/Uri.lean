import Lean.Uri

open Lean.Uri

/- Uri character escaping includes UTF-8 encoding for the 😵‍💫 char! -/
#eval toFileUri "c:/temp/test.xml?😵‍💫=2022"

/- round trip test -/
#eval unescapeUri (toFileUri "c:/temp/test.xml?😵‍💫=2022")

/- and to System.FilePath -/
#eval fileUriToPath (toFileUri "c:/temp/test.xml?😵‍💫=2022")

