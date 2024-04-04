
#eval ("abc" ++ "cde").length
#eval ("abcd".mkIterator.nextn 2).remainingToString
#eval ("abcd".mkIterator.nextn 10).remainingToString
#eval "αβ".length
#eval "αβcc".mkIterator.pos
#eval "αβcc".mkIterator.next.pos
#eval "αβcc".mkIterator.next.next.pos
#eval "αβcc".mkIterator.next.setCurr 'a'
#eval "αβcd".mkIterator.toEnd.pos

#eval "012".splitOn "12"
#eval "007".splitOn "07"
#eval "ababcab".splitOn "abc"
#eval "αbαbcαbcαααbcα".splitOn "αb"
#eval "αbαbcαbcαααbcα".splitOn "αbcα"
#eval "here is some text ".splitOn
#eval "here is some text ".splitOn "some"
#eval "here is some text ".splitOn ""
#eval "ababacabac".splitOn  "aba"
