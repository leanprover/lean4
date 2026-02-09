module

def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'

#guard "education".replace isVowel "☃!" = "☃!d☃!c☃!t☃!☃!n"
#guard "red green blue".replace "e" "" = "rd grn blu"
#guard "red green blue".replace 'e' "" = "rd grn blu"
#guard "red green blue".replace "ee" "E" = "red grEn blue"
#guard "red green blue".replace "e" "E" = "rEd grEEn bluE"
#guard "abc".replace "" "k" = "kakbkck"
#guard "ℕ".replace "" "z" = "zℕz"
#guard "𝔸".replace "" "z" = "z𝔸z"
#guard "v̂".replace "" "z" = "zvẑz"
#guard "aaaaa".replace "aa" "b" = "bba"
#guard "v̂fℚo".replace ("ℕfℚoℤ".toSlice.drop 1 |>.dropEnd 1) ("☃🔭🌌".toSlice.dropEnd 1 |>.drop 1) = "v̂🔭"
#guard ("abcde".toSlice.drop 1).replace (· == 'c') "C" = "bCde"
#guard (("ac  bc  cc  cd".toSlice.split "  ").map (·.replace 'c' "C") |>.toList) = ["aC", "bC", "CC", "Cd"]
#guard "red green blue".replace (fun c => c == 'u' || c == 'e') "" = "rd grn bl"
#guard "aab".replace "ab" "X" = "aX"
#guard " ℚℚ\n ".replace "ℚ\n" "\n" = " ℚ\n "
