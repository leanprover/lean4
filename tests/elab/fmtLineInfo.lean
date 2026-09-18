import Lean.Fmt.FmtM.LineInfo

/-!
Tests the line information collected by the auto-formatter: `collectLineInfos` and
`collectSyntaxLineInfos`.
-/

open Lean Lean.Fmt

-- Extracts (length, indentation, text) for each line.
def lineInfoData (s : String) : Array (Nat × Nat × String) :=
  (collectLineInfos s.toSlice).map fun info =>
    (info.length, info.indentation, info.range.toString)

-- Extracts (length, indentation, line, startPos.byteIdx, endPos.byteIdx) for each line.
def syntaxLineInfoData (stx : Lean.Syntax) : Array (Nat × Nat × String × Nat × Nat) :=
  (collectSyntaxLineInfos stx).map fun info =>
    (info.length, info.indentation, info.line, info.startPos.byteIdx, info.endPos.byteIdx)

-- Extracts (start.byteIdx, stop.byteIdx) of every token range of every line.
def syntaxLineTokenData (stx : Lean.Syntax) : Array (Array (Nat × Nat)) :=
  (collectSyntaxLineInfos stx).map fun info =>
    info.tokenRanges.map fun range => (range.start.byteIdx, range.stop.byteIdx)

-- Constructs an atom with the given value and trailing whitespace.
private def mkAtomTrailing (val trailing : String) : Lean.Syntax :=
  .atom (SourceInfo.original "".toRawSubstring ⟨0⟩ trailing.toRawSubstring ⟨0⟩) val

-- ===== collectLineInfos =====

-- Empty string: one line with length 0 and empty range.
#guard lineInfoData "" = #[(0, 0, "")]

-- Single line without newline.
#guard lineInfoData "hello" = #[(5, 0, "hello")]

-- Leading spaces count toward both length and indentation.
#guard lineInfoData "  hello" = #[(7, 2, "  hello")]

-- Multiple lines split at '\n'.
#guard lineInfoData "hello\nworld" = #[(5, 0, "hello"), (5, 0, "world")]

-- Trailing '\n' produces an empty last line.
#guard lineInfoData "abc\n" = #[(3, 0, "abc"), (0, 0, "")]

-- Line of only spaces: indentation equals length.
#guard lineInfoData "   " = #[(3, 3, "   ")]

-- Spaces after a non-space character don't count toward indentation.
#guard lineInfoData "  ab cd" = #[(7, 2, "  ab cd")]

-- Trailing spaces count toward length but not indentation.
#guard lineInfoData "hello  " = #[(7, 0, "hello  ")]

-- Multiple consecutive newlines produce empty intermediate lines.
#guard lineInfoData "\n\n" = #[(0, 0, ""), (0, 0, ""), (0, 0, "")]

-- Two indented lines.
#guard lineInfoData "  hello\n  world" = #[(7, 2, "  hello"), (7, 2, "  world")]

-- Three lines, the middle one empty.
#guard lineInfoData "a\n\nb" = #[(1, 0, "a"), (0, 0, ""), (1, 0, "b")]

-- ===== collectSyntaxLineInfos =====
-- Assumption: leading is always empty, Syntax.node has no SourceInfo.

-- .missing produces a single empty line at position 0.
#guard syntaxLineInfoData .missing = #[(0, 0, "", 0, 0)]

-- Single atom with SourceInfo.none: byte positions track the atom value.
#guard syntaxLineInfoData (.atom .none "hello") = #[(5, 0, "hello", 0, 5)]

-- Indented atom: leading spaces of a token value do not count toward indentation.
#guard syntaxLineInfoData (.atom .none "  hello") = #[(7, 0, "  hello", 0, 7)]

-- Empty atom is a no-op.
#guard syntaxLineInfoData (.atom .none "") = #[(0, 0, "", 0, 0)]

-- Ident node uses rawVal.toString.
#guard syntaxLineInfoData (.ident .none "hello".toRawSubstring `hello []) = #[(5, 0, "hello", 0, 5)]

-- Node with two adjacent atoms: contents are merged on the same pending line.
#guard syntaxLineInfoData (.node .none `null #[.atom .none "a", .atom .none "b"])
  = #[(2, 0, "ab", 0, 2)]

-- Atom with trailing space extends the pending line.
-- "hello " occupies bytes [0, 6).
#guard syntaxLineInfoData (mkAtomTrailing "hello" " ") = #[(6, 0, "hello ", 0, 6)]

-- Trailing containing a newline splits into two lines.
-- Source: "hello" (bytes [0,5)) + " \n" (bytes [5,7)) + "world" (bytes [7,12))
-- Line 1: "hello " occupies bytes [0, 6) (the '\n' is at byte 6).
-- Line 2: "world" occupies bytes [7, 12).
#guard syntaxLineInfoData (.node .none `null #[
    mkAtomTrailing "hello" " \n",
    .atom .none "world"
  ]) = #[(6, 0, "hello ", 0, 6), (5, 0, "world", 7, 12)]

-- The indentation of the second line is accumulated from the trailing of the first atom.
-- Source: "  hello" (bytes [0,7)) + "\n  " (bytes [7,10)) + "world" (bytes [10,15))
-- Line 1: "  hello" (the leading spaces are part of the token value), startPos=0, endPos=7.
-- Line 2: "  world" (indentation "  " from trailing + "world"), startPos=8, endPos=15.
#guard syntaxLineInfoData (.node .none `null #[
    mkAtomTrailing "  hello" "\n  ",
    .atom .none "world"
  ]) = #[(7, 0, "  hello", 0, 7), (7, 2, "  world", 8, 15)]

-- Three tokens across two lines: "a b" + "\n" + "c"
-- "a" = byte [0,1), " b" (trailing of a) -> combined "a b" at [0,3), '\n' at byte 3,
-- "c" = bytes [4,5).
#guard syntaxLineInfoData (.node .none `null #[
    mkAtomTrailing "a" " b\n",
    .atom .none "c"
  ]) = #[(3, 0, "a b", 0, 3), (1, 0, "c", 4, 5)]

-- When the pending line is all spaces (from trailing) and the next atom starts with spaces,
-- only the spaces from the trailing count toward indentation.
-- Source: "" (atom) + "\n  " (trailing, bytes [0,3)) + "  hello" (atom, bytes [3,10))
--   '\n' is byte 0; "  " (indentation) spans bytes [1,3); "  hello" spans bytes [3,10).
-- Line 1: "" (before '\n'), length=0, indentation=0, startPos=0, endPos=0.
-- Line 2: "    hello" (merged "  " + "  hello"), length=9, indentation=2, startPos=1, endPos=10.
#guard syntaxLineInfoData (.node .none `null #[
    mkAtomTrailing "" "\n  ",
    .atom .none "  hello"
  ]) = #[(0, 0, "", 0, 0), (9, 2, "    hello", 1, 10)]

-- ===== collectSyntaxLineInfos token ranges =====
-- Every line reports the full range of each token it is covered by, so a multi-line token is
-- reported unchanged on every one of its lines.

-- .missing contributes no tokens.
#guard syntaxLineTokenData .missing = #[#[]]

-- A single atom is a token spanning its whole value.
#guard syntaxLineTokenData (.atom .none "hello") = #[#[(0, 5)]]

-- An empty atom is still a token, albeit an empty one.
#guard syntaxLineTokenData (.atom .none "") = #[#[(0, 0)]]

-- Idents are tokens too.
#guard syntaxLineTokenData (.ident .none "hello".toRawSubstring `hello []) = #[#[(0, 5)]]

-- Adjacent atoms produce two tokens on the same line.
#guard syntaxLineTokenData (.node .none `null #[.atom .none "a", .atom .none "b"])
  = #[#[(0, 1), (1, 2)]]

-- Trailing whitespace is not part of the token.
#guard syntaxLineTokenData (mkAtomTrailing "hello" " ") = #[#[(0, 5)]]

-- Whitespace-only advances contribute no tokens.
-- Source: "hello" (bytes [0,5)) + " \n" (bytes [5,7)) + "world" (bytes [7,12))
#guard syntaxLineTokenData (.node .none `null #[
    mkAtomTrailing "hello" " \n",
    .atom .none "world"
  ]) = #[#[(0, 5)], #[(7, 12)]]

-- A token spanning two lines is reported with its full range on both of them.
-- Source: "a" [0,1) + '\n' at byte 1 + "b" [2,3); the token spans [0,3).
#guard syntaxLineTokenData (.atom .none "a\nb") = #[#[(0, 3)], #[(0, 3)]]

-- Likewise for a line that is fully covered by a token.
-- Source: "a" [0,1) + "b" [2,3) + "c" [4,5); the token spans [0,5).
#guard syntaxLineTokenData (.atom .none "a\nb\nc") = #[#[(0, 5)], #[(0, 5)], #[(0, 5)]]

-- A line ending in a multi-line token reports both that token and the one following it.
-- Source: "a\nb" [0,3) + "c" [3,4).
#guard syntaxLineTokenData (.node .none `null #[.atom .none "a\nb", .atom .none "c"])
  = #[#[(0, 3)], #[(0, 3), (3, 4)]]

-- A token ending in a newline also covers the empty line after it.
-- Source: "a" [0,1) + '\n' at byte 1; the token spans [0,2).
#guard syntaxLineTokenData (.atom .none "a\n") = #[#[(0, 2)], #[(0, 2)]]
