import Init.System.Uri

open System.Uri

/- Uri character escaping includes UTF-8 encoding for the 😵‍💫 char! -/
#eval toFileUri "/temp/test.xml?😵‍💫=2022"

/- round trip test -/
#eval unescapeUri (toFileUri "/temp/test.xml?😵‍💫=2022")

/- and to System.FilePath -/
#eval fileUriToPath (toFileUri "/temp/test.xml?😵‍💫=2022")

/- escaped percent -/
#eval unescapeUri "/temp/test%%.xml"

/- invalid escape followed by valid escapes -/
#eval unescapeUri "file://test%xx/%3Fa%3D123"

/- tilde is NOT escaped -/
#eval toFileUri "~/git/lean4"
