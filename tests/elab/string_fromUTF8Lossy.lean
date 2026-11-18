/-!
Tests `String.fromUTF8Lossy` on valid input of every encoding length and on every kind of invalid
input, and checks that its public lemmas apply.
-/

def lossy (l : List UInt8) : String :=
  String.fromUTF8Lossy l.toByteArray

/-! Docstring examples -/

#guard lossy [0x4C, 0xE2, 0x88, 0x83, 0x4E] = "L∃N"
#guard lossy [0x61, 0xFF, 0x62] = "a�b"
#guard lossy [0x61, 0xE2, 0x88, 0x62] = "a�b"
#guard lossy [0x61, 0xED, 0xA0, 0x80, 0x62] = "a�b"
#guard lossy [0x61, 0x80, 0x80, 0x80, 0x62] = "a�b"
#guard lossy [0xFF, 0xFF] = "��"

/-! Valid input, including the smallest and largest scalar value of each encoding length -/

#guard lossy [] = ""
#guard lossy [0x00] = "\x00"
#guard lossy [0x7F] = "\x7f"
#guard lossy [0xC2, 0x80] = "\u0080"
#guard lossy [0xDF, 0xBF] = "߿"
#guard lossy [0xE0, 0xA0, 0x80] = "ࠀ"
#guard lossy [0xED, 0x9F, 0xBF] = "퟿"
#guard lossy [0xEE, 0x80, 0x80] = ""
#guard lossy [0xEF, 0xBF, 0xBF] = "￿"
#guard lossy [0xF0, 0x90, 0x80, 0x80] = "𐀀"
#guard lossy [0xF4, 0x8F, 0xBF, 0xBF] = .singleton (Char.ofNat 0x10FFFF)
#guard String.fromUTF8Lossy "aé€😀".toByteArray = "aé€😀"

/-! Bytes that never occur in UTF-8 -/

#guard lossy [0xC0] = "�"
#guard lossy [0xC1, 0x41] = "�A"
#guard lossy [0xF5, 0x80, 0x80, 0x80] = "�"
#guard lossy [0xF8, 0x88, 0x80, 0x80, 0x80] = "�"
#guard lossy [0xFE, 0x41, 0xFF] = "�A�"

/-! Overlong encodings -/

#guard lossy [0xC0, 0x80] = "�"
#guard lossy [0xC1, 0xBF] = "�"
#guard lossy [0xE0, 0x80, 0x80] = "�"
#guard lossy [0xE0, 0x9F, 0xBF] = "�"
#guard lossy [0xF0, 0x80, 0x80, 0x80] = "�"
#guard lossy [0xF0, 0x8F, 0xBF, 0xBF] = "�"

/-! Surrogates and code points above `U+10FFFF` -/

#guard lossy [0xED, 0xA0, 0x80] = "�"
#guard lossy [0xED, 0xBF, 0xBF] = "�"
#guard lossy [0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80] = "��"
#guard lossy [0xF4, 0x90, 0x80, 0x80] = "�"
#guard lossy [0xF7, 0xBF, 0xBF, 0xBF] = "�"

/-! Truncated sequences, at the end and before a byte that is not a continuation byte -/

#guard lossy [0xC3] = "�"
#guard lossy [0xE2, 0x88] = "�"
#guard lossy [0xF0, 0x9F, 0x98] = "�"
#guard lossy [0xC3, 0x41] = "�A"
#guard lossy [0xF0, 0x9F, 0x41] = "�A"
#guard lossy [0xE2, 0x88, 0xC3, 0xA9] = "�é"
#guard lossy [0xC3, 0xC3] = "��"
#guard lossy [0xF0, 0x9F, 0x98, 0xF0, 0x9F, 0x98, 0x80] = "�😀"

/-! Stray continuation bytes, which are merged into the preceding `�` -/

#guard lossy [0x80] = "�"
#guard lossy [0xBF, 0x80, 0xBF] = "�"
#guard lossy [0xC3, 0xA9, 0xA9] = "é�"
#guard lossy [0xF0, 0x9F, 0x98, 0x80, 0x80, 0x80, 0x41] = "😀�A"
#guard lossy [0x41, 0x80, 0x42, 0x80, 0x43] = "A�B�C"
#guard lossy [0xFF, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80] = "�"
-- An invalid sequence absorbs all following continuation bytes, even beyond its encoded length.
#guard lossy [0xE0, 0x80, 0x80, 0x80, 0x80] = "�"

/-! Public lemmas -/

example : String.fromUTF8Lossy ByteArray.empty = "" := by simp

example (l : List Char) : String.fromUTF8Lossy l.utf8Encode = String.ofList l := by simp

example (s : String) : String.fromUTF8Lossy s.toByteArray = s := by simp

example (l : List Char) (b : ByteArray) :
    String.fromUTF8Lossy (l.utf8Encode ++ b) = String.ofList l ++ String.fromUTF8Lossy b :=
  String.fromUTF8Lossy_utf8Encode_append

example (b : ByteArray) (hb : ∀ h : 0 < b.size, ¬ b[0].isUTF8ContinuationByte) :
    String.fromUTF8Lossy ([0xED, 0xBF, 0x80].toByteArray ++ b) =
      String.singleton '�' ++ String.fromUTF8Lossy b :=
  String.fromUTF8Lossy_surrogate_append (by decide) (by decide) hb
