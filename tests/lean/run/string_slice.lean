module
import Std.Data.HashSet.Basic

/-!
Tests for `String.Slice` functions
-/

#guard "".toSlice.isEmpty = true
#guard " ".toSlice.isEmpty = false
#guard (" ".toSlice.drop 1).isEmpty = true

#guard "abc".toSlice == "abc".toSlice
#guard "abcdefg".toSlice.dropEnd 4 == "abc".toSlice
#guard "abcdefg".toSlice.dropEnd 3 != "abc".toSlice

#guard "red green blue".toSlice.startsWith "red" = true
#guard "red green blue".toSlice.startsWith "green" = false
#guard "red green blue".toSlice.startsWith "" = true
#guard "red green blue".toSlice.startsWith 'r' = true
#guard "red green blue".toSlice.startsWith Char.isLower = true
#guard "red green blue".toSlice.startsWith (· = 'r') = true
#guard "red green blue".toSlice.startsWith (· = 's') = false

#guard ("coffee tea water".toSlice.split Char.isWhitespace).toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]
#guard ("coffee tea water".toSlice.split ' ').toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]
#guard ("coffee tea water".toSlice.split " tea ").toList == ["coffee".toSlice, "water".toSlice]
#guard ("baaab".toSlice.split "aa").toList == ["b".toSlice, "ab".toSlice]
#guard ("aababaaba".toSlice.split "ab").toList == ["a".toSlice, "".toSlice, "a".toSlice, "a".toSlice]

#guard ("coffee tea water".toSlice.splitInclusive Char.isWhitespace).toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]
#guard ("coffee tea water".toSlice.splitInclusive ' ').toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]
#guard ("coffee tea water".toSlice.splitInclusive " tea ").toList == ["coffee tea ".toSlice, "water".toSlice]
#guard ("a".toSlice.splitInclusive (fun (_ : Char) => true)).toList == ["a".toSlice]
#guard ("baaab".toSlice.splitInclusive "aa").toList == ["baa".toSlice, "ab".toSlice]
#guard ("aababaaba".toSlice.splitInclusive "ab").toList == ["aab".toSlice, "ab".toSlice, "aab".toSlice, "a".toSlice]

#guard "red green blue".toSlice.drop 4 == "green blue".toSlice
#guard "red green blue".toSlice.drop 10 == "blue".toSlice
#guard "red green blue".toSlice.drop 50 == "".toSlice

#guard "red green blue".toSlice.dropWhile Char.isLower == " green blue".toSlice
#guard "red green blue".toSlice.dropWhile 'r' == "ed green blue".toSlice
#guard "red red green blue".toSlice.dropWhile "red " == "green blue".toSlice
#guard "red green blue".toSlice.dropWhile (fun (_ : Char) => true) == "".toSlice
#guard "rrrrred green blue".toSlice.dropWhile (· = 'r') == "ed green blue".toSlice

#guard "abc".toSlice.trimAsciiStart == "abc".toSlice
#guard "   abc".toSlice.trimAsciiStart == "abc".toSlice
#guard "abc \t  ".toSlice.trimAsciiStart == "abc \t  ".toSlice
#guard "  abc   ".toSlice.trimAsciiStart == "abc   ".toSlice
#guard "abc\ndef\n".toSlice.trimAsciiStart == "abc\ndef\n".toSlice

#guard "red green blue".toSlice.take 3 == "red".toSlice
#guard "red green blue".toSlice.take 1 == "r".toSlice
#guard "red green blue".toSlice.take 0 == "".toSlice
#guard "red green blue".toSlice.take 100 == "red green blue".toSlice

#guard "red green blue".toSlice.takeWhile Char.isLower == "red".toSlice
#guard "red green blue".toSlice.takeWhile 'r' == "r".toSlice
#guard "red red green blue".toSlice.takeWhile "red " == "red red ".toSlice
#guard "red green blue".toSlice.takeWhile (fun (_ : Char) => true) == "red green blue".toSlice

#guard (" ".toSlice.dropWhile ' ' |>.takeWhile Char.isLower) == "".toSlice
#guard (" ".toSlice.dropWhile ' ' |>.takeEndWhile Char.isLower) == "".toSlice
#guard ("∃a∃".toSlice.drop 1 |>.takeWhile Char.isLower) == "a".toSlice
#guard ("∃a∃".toSlice.dropEnd 1 |>.takeEndWhile Char.isLower) == "a".toSlice

#guard "red green blue".toSlice.dropPrefix? "red " == some "green blue".toSlice
#guard "red green blue".toSlice.dropPrefix? "reed " == none
#guard "red green blue".toSlice.dropPrefix? 'r' == some "ed green blue".toSlice
#guard "red green blue".toSlice.dropPrefix? Char.isLower == some "ed green blue".toSlice

#guard "red green blue".toSlice.dropPrefix "red " == "green blue".toSlice
#guard "red green blue".toSlice.dropPrefix "reed " == "red green blue".toSlice
#guard "red green blue".toSlice.dropPrefix 'r' == "ed green blue".toSlice
#guard "red green blue".toSlice.dropPrefix Char.isLower == "ed green blue".toSlice

#guard ("coffee tea water".toSlice.find? Char.isWhitespace).map (·.get!) == some ' '
#guard "tea".toSlice.find? (fun (c : Char) => c == 'X') == none
#guard ("coffee tea water".toSlice.find? "tea").map (·.get!) == some 't'

#guard "coffee tea water".toSlice.contains Char.isWhitespace = true
#guard "tea".toSlice.contains (fun (c : Char) => c == 'X') = false
#guard "coffee tea water".toSlice.contains "tea" = true

#guard "brown".toSlice.all Char.isLower = true
#guard "brown and orange".toSlice.all Char.isLower = false
#guard "aaaaaa".toSlice.all 'a' = true
#guard "aaaaaa".toSlice.all "aa" = true
#guard "aaaaaaa".toSlice.all "aa" = false

#guard "red green blue".toSlice.endsWith "blue" = true
#guard "red green blue".toSlice.endsWith "green" = false
#guard "red green blue".toSlice.endsWith "" = true
#guard "red green blue".toSlice.endsWith 'e' = true
#guard "red green blue".toSlice.endsWith Char.isLower = true
#guard "red green blue".toSlice.endsWith (· = 'e') = true
#guard "red green blue".toSlice.endsWith (· = 'f') = false

#guard ("coffee tea water".toSlice.revSplit Char.isWhitespace).toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]
#guard ("coffee tea water".toSlice.revSplit ' ').toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]

#guard "red green blue".toSlice.dropEnd 5 == "red green".toSlice
#guard "red green blue".toSlice.dropEnd 11 == "red".toSlice
#guard "red green blue".toSlice.dropEnd 50 == "".toSlice

#guard "red green blue".toSlice.dropEndWhile Char.isLower == "red green ".toSlice
#guard "red green blue".toSlice.dropEndWhile 'e' == "red green blu".toSlice
#guard "red green blue".toSlice.dropEndWhile (fun (_ : Char) => true) == "".toSlice
#guard "red green blueeeeeee".toSlice.dropEndWhile (· = 'e') == "red green blu".toSlice

#guard "abc".toSlice.trimAsciiEnd == "abc".toSlice
#guard "   abc".toSlice.trimAsciiEnd == "   abc".toSlice
#guard "abc \t  ".toSlice.trimAsciiEnd == "abc".toSlice
#guard "  abc   ".toSlice.trimAsciiEnd == "  abc".toSlice
#guard "abc\ndef\n".toSlice.trimAsciiEnd == "abc\ndef".toSlice

#guard "red green blue".toSlice.takeEnd 4 == "blue".toSlice
#guard "red green blue".toSlice.takeEnd 1 == "e".toSlice
#guard "red green blue".toSlice.takeEnd 0 == "".toSlice
#guard "red green blue".toSlice.takeEnd 100 == "red green blue".toSlice

#guard "red green blue".toSlice.takeEndWhile Char.isLower == "blue".toSlice
#guard "red green blue".toSlice.takeEndWhile 'e' == "e".toSlice
#guard "red green blue".toSlice.takeEndWhile (fun (_ : Char) => true) == "red green blue".toSlice

#guard "red green blue".toSlice.dropSuffix? " blue" == some "red green".toSlice
#guard "red green blue".toSlice.dropSuffix? "bluu " == none
#guard "red green blue".toSlice.dropSuffix? 'e' == some "red green blu".toSlice
#guard "red green blue".toSlice.dropSuffix? Char.isLower == some "red green blu".toSlice

#guard "red green blue".toSlice.dropSuffix " blue" == "red green".toSlice
#guard "red green blue".toSlice.dropSuffix "bluu " == "red green blue".toSlice
#guard "red green blue".toSlice.dropSuffix 'e' == "red green blu".toSlice
#guard "red green blue".toSlice.dropSuffix Char.isLower == "red green blu".toSlice

#guard "abc".toSlice.trimAscii == "abc".toSlice
#guard "   abc".toSlice.trimAscii == "abc".toSlice
#guard "abc \t  ".toSlice.trimAscii == "abc".toSlice
#guard "  abc   ".toSlice.trimAscii == "abc".toSlice
#guard "abc\ndef\n".toSlice.trimAscii == "abc\ndef".toSlice


#guard ({} : Std.HashSet _).insert "abc".toSlice |>.contains "abc".toSlice
#guard (({} : Std.HashSet _).insert "abc".toSlice |>.insert "abc".toSlice |>.size) == 1

#guard "abc".toSlice ≤ "abc".toSlice
#guard "abc".toSlice < "abcd".toSlice
#guard "abc".toSlice < "zbc".toSlice
#guard "".toSlice < "zbc".toSlice
#guard "".toSlice ≤ "".toSlice

#guard "abc".toSlice.chars.toList = ['a', 'b', 'c']
#guard "ab∀c".toSlice.chars.toList = ['a', 'b', '∀', 'c']

#guard "abc".toSlice.revChars.toList = ['c', 'b', 'a']
#guard "ab∀c".toSlice.revChars.toList = ['c', '∀', 'b', 'a']

#guard ("abc".toSlice.positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', 'c']
#guard ("abc".toSlice.positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2]
#guard ("ab∀c".toSlice.positions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['a', 'b', '∀', 'c']
#guard ("ab∀c".toSlice.positions.map (·.val.offset.byteIdx) |>.toList) = [0, 1, 2, 5]

#guard ("abc".toSlice.revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', 'b', 'a']
#guard ("abc".toSlice.revPositions.map (·.val.offset.byteIdx) |>.toList) = [2, 1, 0]
#guard ("ab∀c".toSlice.revPositions.map (fun ⟨p, h⟩ => p.get h) |>.toList) = ['c', '∀', 'b', 'a']
#guard ("ab∀c".toSlice.revPositions.map (·.val.offset.byteIdx) |>.toList) = [5, 2, 1, 0]

#guard "abc".toSlice.bytes.toList = [97, 98, 99]
#guard "ab∀c".toSlice.bytes.toList = [97, 98, 226, 136, 128, 99]

#guard "abc".toSlice.revBytes.toList = [99, 98, 97]
#guard "ab∀c".toSlice.revBytes.toList = [99, 128, 136, 226, 98, 97]

#guard "foo\r\nbar\n\nbaz\n".toSlice.lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz".toSlice]
#guard "foo\r\nbar\n\nbaz".toSlice.lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz".toSlice]
#guard "foo\r\nbar\n\nbaz\r".toSlice.lines.toList  == ["foo".toSlice, "bar".toSlice, "".toSlice, "baz\r".toSlice]

#guard "coffee tea water".toSlice.foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 2
#guard "coffee tea and water".toSlice.foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 3
#guard "coffee tea water".toSlice.foldl (·.push ·) "" = "coffee tea water"

#guard "coffee tea water".toSlice.foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 2
#guard "coffee tea and water".toSlice.foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 3
#guard "coffee tea water".toSlice.foldr (fun c s => s.push c) "" = "retaw aet eeffoc"

#guard "".toSlice.isNat = false
#guard "0".toSlice.isNat = true
#guard "5".toSlice.isNat = true
#guard "05".toSlice.isNat = true
#guard "587".toSlice.isNat = true
#guard "-587".toSlice.isNat = false
#guard " 5".toSlice.isNat = false
#guard "2+3".toSlice.isNat = false
#guard "0xff".toSlice.isNat = false

#guard "".toSlice.toNat? = none
#guard "0".toSlice.toNat? = some 0
#guard "5".toSlice.toNat? = some 5
#guard "587".toSlice.toNat? = some 587
#guard "-587".toSlice.toNat? = none
#guard " 5".toSlice.toNat? = none
#guard "2+3".toSlice.toNat? = none
#guard "0xff".toSlice.toNat? = none

#guard "0".toSlice.toNat! = 0
#guard "5".toSlice.toNat! = 5
#guard "587".toSlice.toNat! = 587

#guard "abc".toSlice.front? = some 'a'
#guard "".toSlice.front? = none

#guard "abc".toSlice.front = 'a'
#guard "".toSlice.front = (default : Char)

#guard "abc".toSlice.back? = some 'c'
#guard "".toSlice.back? = none

#guard "abc".toSlice.back = 'c'
#guard "".toSlice.back = (default : Char)

section
open String.Slice.Pattern

#guard (ToForwardSearcher.toSearcher "" "".toSlice).toList == [.matched "".toSlice.startPos "".toSlice.startPos]
#guard (ToForwardSearcher.toSearcher "" "abc".toSlice).toList == [
  .matched ("abc".toSlice.pos ⟨0⟩ (by decide)) ("abc".toSlice.pos ⟨0⟩ (by decide)),
  .rejected ("abc".toSlice.pos ⟨0⟩ (by decide)) ("abc".toSlice.pos ⟨1⟩ (by decide)),
  .matched ("abc".toSlice.pos ⟨1⟩ (by decide)) ("abc".toSlice.pos ⟨1⟩ (by decide)),
  .rejected ("abc".toSlice.pos ⟨1⟩ (by decide)) ("abc".toSlice.pos ⟨2⟩ (by decide)),
  .matched ("abc".toSlice.pos ⟨2⟩ (by decide)) ("abc".toSlice.pos ⟨2⟩ (by decide)),
  .rejected ("abc".toSlice.pos ⟨2⟩ (by decide)) ("abc".toSlice.pos ⟨3⟩ (by decide)),
  .matched ("abc".toSlice.pos ⟨3⟩ (by decide)) ("abc".toSlice.pos ⟨3⟩ (by decide)),
]

end

#guard ("".toSlice.split "").toList == ["".toSlice, "".toSlice]
#guard ("abc".toSlice.split "").toList == ["".toSlice, "a".toSlice, "b".toSlice, "c".toSlice, "".toSlice]

#guard " ".find (·.isWhitespace) = " ".startPos
#guard " ".find (· = ' ') = " ".startPos
#guard " ".startsWith (·.isWhitespace) = true
#guard " ".startsWith (· = ' ') = true
#guard " ".revFind? (·.isWhitespace) = some " ".startPos
#guard " ".revFind? (· = ' ') = some " ".startPos
#guard " ".endsWith (·.isWhitespace) = true
#guard " ".endsWith (· = ' ') = true
