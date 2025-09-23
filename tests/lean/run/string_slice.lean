module

/-!
Tests for `String.Slice` functions
-/

#guard "".toSlice.isEmpty = true
#guard " ".toSlice.isEmpty = false
#guard (" ".toSlice.drop 1).isEmpty = true

#guard "red green blue".toSlice.startsWith "red" = true
#guard "red green blue".toSlice.startsWith "green" = false
#guard "red green blue".toSlice.startsWith "" = true
#guard "red green blue".toSlice.startsWith 'r' = true
#guard "red green blue".toSlice.startsWith Char.isLower = true

#guard ("coffee tea water".toSlice.split Char.isWhitespace).allowNontermination.toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]
#guard ("coffee tea water".toSlice.split ' ').allowNontermination.toList == ["coffee".toSlice, "tea".toSlice, "water".toSlice]
#guard ("coffee tea water".toSlice.split " tea ").allowNontermination.toList == ["coffee".toSlice, "water".toSlice]

#guard ("coffee tea water".toSlice.splitInclusive Char.isWhitespace).allowNontermination.toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]
#guard ("coffee tea water".toSlice.splitInclusive ' ').allowNontermination.toList == ["coffee ".toSlice, "tea ".toSlice, "water".toSlice]
#guard ("coffee tea water".toSlice.splitInclusive " tea ").allowNontermination.toList == ["coffee tea ".toSlice, "water".toSlice]
#guard ("a".toSlice.splitInclusive (fun (_ : Char) => true)).allowNontermination.toList == ["a".toSlice]

#guard "red green blue".toSlice.drop 4 == "green blue".toSlice
#guard "red green blue".toSlice.drop 10 == "blue".toSlice
#guard "red green blue".toSlice.drop 50 == "".toSlice

#guard "red green blue".toSlice.dropWhile Char.isLower == " green blue".toSlice
#guard "red green blue".toSlice.dropWhile 'r' == "ed green blue".toSlice
#guard "red red green blue".toSlice.dropWhile "red " == "green blue".toSlice
#guard "red green blue".toSlice.dropWhile (fun (_ : Char) => true) == "".toSlice

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

#guard "red green blue".toSlice.endsWith "blue" = true
#guard "red green blue".toSlice.endsWith "green" = false
#guard "red green blue".toSlice.endsWith "" = true
#guard "red green blue".toSlice.endsWith 'e' = true
#guard "red green blue".toSlice.endsWith Char.isLower = true

#guard ("coffee tea water".toSlice.revSplit Char.isWhitespace).allowNontermination.toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]
#guard ("coffee tea water".toSlice.revSplit ' ').allowNontermination.toList == ["water".toSlice, "tea".toSlice, "coffee".toSlice]

#guard "red green blue".toSlice.dropEnd 5 == "red green".toSlice
#guard "red green blue".toSlice.dropEnd 11 == "red".toSlice
#guard "red green blue".toSlice.dropEnd 50 == "".toSlice

#guard "red green blue".toSlice.dropEndWhile Char.isLower == "red green ".toSlice
#guard "red green blue".toSlice.dropEndWhile 'e' == "red green blu".toSlice
#guard "red green blue".toSlice.dropEndWhile (fun (_ : Char) => true) == "".toSlice

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

-- TODO: beq
-- TODO: hashmap
-- TODO: LT/ord
-- TODO: chars/revchars
-- TODO: pos/revpos
-- TODO: bytes/revbytes
-- TODO: lines
