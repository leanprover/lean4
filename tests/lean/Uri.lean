import Std.System.Uri

open System.Uri

/- Uri character escaping includes UTF-8 encoding for the 😵 char! -/
#eval pathToUri "/temp/test.xml?😵=2022"

/- round trip test -/
#eval fileUriToPath? (pathToUri "/temp/test.xml?😵=2022")

/- invalid file uri -/
#eval fileUriToPath? "invalid"

/- escaped percent -/
#eval unescapeUri "/temp/test%25.xml"

/- invalid percents -/
#eval unescapeUri "%%"

/- invalid escape followed by valid escapes -/
#eval unescapeUri "file://test%xx/%3Fa%3D123"

/- tilde is NOT escaped -/
#eval pathToUri "~/git/lean4"

/- trailing truncated escape ignored -/
#eval unescapeUri "lean%4"

/- Nothing to unescape -/
#eval unescapeUri "Lean1234😵"

def testWindowsDriveLetterEscaping : String :=
  if System.Platform.isWindows then
    let x : System.FilePath := "C:" / "Temp" / "test.lean"
    let r := pathToUri x
    if r == "file:///c%3a/temp/test.lean" then
      match fileUriToPath? r with
      | none => "testWindowsDriveLetterEscaping fileUriToPath? returned none"
      | some y =>
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
