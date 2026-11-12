/-!
Tests for `Substring.Raw.splitOn`, in particular that a partial match of the separator does not
cause a following real match to be missed (e.g. `"aab"` split on `"ab"`).
-/

def splitStrs (s : Substring.Raw) (sep : String) : List String :=
  (s.splitOn sep).map (·.toString)

-- Regression: the partial match `a` must not swallow the start of the real match `ab`.
#guard splitStrs "aab".toRawSubstring "ab" = ["a", ""]
#guard splitStrs "xaabx".toRawSubstring "ab" = ["xa", "x"]
#guard splitStrs "aaab".toRawSubstring "aab" = ["a", ""]
#guard splitStrs "abababc".toRawSubstring "ababc" = ["ab", ""]
#guard splitStrs "∀∀∃".toRawSubstring "∀∃" = ["∀", ""]

-- Basic behavior
#guard splitStrs "here is some text ".toRawSubstring " " = ["here", "is", "some", "text", ""]
#guard splitStrs "here is some text ".toRawSubstring "some" = ["here is ", " text "]
#guard splitStrs "here is some text ".toRawSubstring "" = ["here is some text "]
#guard splitStrs "ababacabac".toRawSubstring "aba" = ["", "bac", "c"]
#guard splitStrs "".toRawSubstring "a" = [""]
#guard splitStrs "a".toRawSubstring "a" = ["", ""]
#guard splitStrs "abc".toRawSubstring "abcd" = ["abc"]

/-- Wraps `s` in padding so that the substring has a nonzero start offset. -/
def padded (s : String) : Substring.Raw :=
  ⟨"aab" ++ s ++ "ab", ⟨3⟩, ⟨3 + s.utf8ByteSize⟩⟩

def cases : List (String × String) :=
  [("aab", "ab"), ("aaab", "aab"), ("abababc", "ababc"), ("ababacabac", "aba"),
   ("here is some text ", " "), ("a,b,,c,", ","), ("L∃∀N∃∀", "∃∀"), ("∀∀∃", "∀∃"),
   ("", "x"), ("abc", "abcd"), ("aaaa", "aa"), ("abcabd", "abd"), ("xyz", "")]

-- `Substring.Raw.splitOn` agrees with `String.splitOn`, also on substrings with a nonzero start.
#guard cases.all fun (s, sep) => splitStrs s.toRawSubstring sep = s.splitOn sep
#guard cases.all fun (s, sep) => splitStrs (padded s) sep = s.splitOn sep

-- All pieces, including empty ones, are substrings of the original string.
#guard cases.all fun (s, sep) => ((padded s).splitOn sep).all (·.str == (padded s).str)

-- An invalid substring (start position in the middle of `∃`) is returned unchanged.
#guard
  let s : Substring.Raw := ⟨"L∃∀N", ⟨2⟩, ⟨7⟩⟩
  (s.splitOn "∀").map (fun p => (p.str, p.startPos, p.stopPos)) = [(s.str, s.startPos, s.stopPos)]
