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

/- trailing truncated escape ignored -/
#eval unescapeUri "lean%4"

def testWindowsDriveLetterEscaping : String :=
  if System.Platform.isWindows then
    let x : System.FilePath := "C:" / "Temp" / "test.lean"
    let r := toFileUri x.normalize.toString
    if r == "file:///c%3a/temp/test.lean" then
      let y := fileUriToPath r
      if y.normalize.toString == x.normalize.toString  then
        "testWindowsDriveLetterEscaping ok"
      else
        s!"testWindowsDriveLetterEscaping '{x.normalize.toString}' != '{y.normalize.toString}'"
    else
      "testWindowsDriveLetterEscaping failed to escape"
  else
    -- skip test on other platforms, drive letters are only a windows thing.
    "testWindowsDriveLetterEscaping ok"

#eval testWindowsDriveLetterEscaping
