import Std.System.Uri

open Lean
open System.Uri

------------------------------------------------------------------------------
-- see https://github.com/python/cpython/blob/main/Lib/test/test_urllib.py

def testEscaping :=
  /- Uri character escaping includes UTF-8 encoding for the 😵 char! -/
  assert! (pathToUri "/temp/test.xml?😵=2022") == "file:///temp/test.xml%3F%F0%9F%98%B5%3D2022"
  /- tilde is NOT escaped -/
  assert! (pathToUri "~/git/lean4") == "file:///~/git/lean4"
  true

def testNeverEscape :=
  let do_not_quote := String.join ["ABCDEFGHIJKLMNOPQRSTUVWXYZ",
                      "abcdefghijklmnopqrstuvwxyz",
                      "0123456789",
                      "_.-~<>\"{}|\\^`"]
  let result := escapeUri do_not_quote
  assert! result == do_not_quote
  true

def testShouldEscape :=
  let controls := String.mk ((List.range 31).map (fun c => Char.ofNat c))
  let should_quote := String.join [controls,
                      "#%[]",
                      (Char.ofNat 127).toString] -- for 0x7F
  assert! should_quote.data.all (λ c =>
    let x := (escapeUri c.toString)
    x.length == 3 && x.take 1 == "%")
  true

def testPartialEscape :=
  assert! (escapeUri "ab[]cd") == "ab%5B%5Dcd"
  true

def testSpaceEscape :=
  assert! (escapeUri " ") == "%20"
  true

def testUnicodeEscape :=
  assert! (escapeUri "😵") == "%F0%9F%98%B5"
  assert! (escapeUri "\u6f22\u5b57") == "%E6%BC%A2%E5%AD%97"
  true

def testRoundTrip :=
  assert! (fileUriToPath? (pathToUri "/temp/test.xml?😵=2022")) == "/temp/test.xml?😵=2022"
  true

def testInvalidFileUri :=
  assert! (fileUriToPath? "invalid") == none
  true

def testUnescapePercent :=
  assert! (unescapeUri "/temp/test%25.xml") == "/temp/test%.xml"
  true

def testUnescapeSinglePercent :=
  assert! (unescapeUri "%") == "%"
  true

def testUnescapeBadHex :=
  assert! (unescapeUri "%xab") == "%xab"
  assert! (unescapeUri "file://test%W9/%3Fa%3D123") == "file://test%W9/?a=123"
  true

def testTruncatedEscape :=
  assert! (unescapeUri "lean%4") == "lean%4"
  true

def testUnescapeUnicode :=
  assert! (unescapeUri "%F0%9F%98%B5") == "😵"
  assert! (unescapeUri "br%C3%BCckner") == "brückner"
  assert! (unescapeUri "br%C3%BCckner") == "brückner"
  assert! (unescapeUri "\u6f22%C3%BC") == "\u6f22\u00fc"
  true

def testUnescapeMixedCase :=
  assert! (unescapeUri "\u00Ab\u006A") == "«j"
  true

def testShouldUnescape :=
  let controls := String.mk ((List.range 31).map (fun c => Char.ofNat c))
  let should_quote := String.join [controls,
                      "#%[]",
                      (Char.ofNat 127).toString] -- for 0x7F
  assert! should_quote == unescapeUri (escapeUri should_quote)
  true

def testWindowsDriveLetter :=
  if System.Platform.isWindows then
    assert! pathToUri ("c:" / "temp") == "file:///c%3A/temp"
    true
  else
    true

def testWindowsDriveLetterRoundTrip :=
  if System.Platform.isWindows then
    let x : System.FilePath := "c:" / "temp" / "test.lean"
    let r := pathToUri x
    let result := if r == "file:///c%3A/temp/test.lean" then
      match fileUriToPath? r with
      | none =>
        "testWindowsDriveLetterEscaping fileUriToPath? returned none"
      | some y =>
        if y.normalize.toString == x.normalize.toString  then
          ""
        else
          s!"testWindowsDriveLetterEscaping '{x.normalize.toString}' != '{y.normalize.toString}'"
    else
      s!"testWindowsDriveLetterEscaping escaped to {r}"
    assert! result == ""
    true
  else
    true

def TestUncRoundTrip :=
  let results := ["file:///c:", "file:////folder/test", "file:///c:/foo/bar/spam.foo"].map (fun p =>
    let result := (match fileUriToPath? p with
      | some uri => unescapeUri (pathToUri uri)
      | none => "fileUriToPath? failed")
    if result == p then
      "ok"
    else
      s!"mismatch {result} != {p}")

  let ok := (results.all (λ c => c == "ok"))
  assert! ok -- s!"the results are not as expected: {results}"
  true


#eval testEscaping &&
      testNeverEscape &&
      testShouldEscape &&
      testRoundTrip &&
      testPartialEscape &&
      testSpaceEscape &&
      testUnicodeEscape &&
      testInvalidFileUri &&
      testUnescapePercent &&
      testUnescapeSinglePercent &&
      testUnescapeBadHex &&
      testTruncatedEscape &&
      testUnescapeUnicode &&
      testUnescapeMixedCase &&
      testShouldUnescape &&
      testWindowsDriveLetterRoundTrip
