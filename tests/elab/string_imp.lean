/-!
Tests evaluation of basic `String` operations: `length`, `++` and `splitOn`.
-/

#eval ("abc" ++ "cde").length
#eval "αβ".length

#eval "012".splitOn "12"
#eval "007".splitOn "07"
#eval "ababcab".splitOn "abc"
#eval "αbαbcαbcαααbcα".splitOn "αb"
#eval "αbαbcαbcαααbcα".splitOn "αbcα"
#eval "here is some text ".splitOn
#eval "here is some text ".splitOn "some"
#eval "here is some text ".splitOn ""
#eval "ababacabac".splitOn  "aba"
