#eval ("abc" ++ "cde").length
#eval ("abcd".mkIterator.nextn 2).remainingToString
#eval ("abcd".mkIterator.nextn 10).remainingToString
#eval "αβ".length
#eval "αβcc".mkIterator.pos
#eval "αβcc".mkIterator.next.pos
#eval "αβcc".mkIterator.next.next.pos
#eval "αβcc".mkIterator.next.setCurr 'a'
#eval "αβcd".mkIterator.toEnd.pos
#eval "ab\n\nfoo bla".lineColumn 0
#eval "ab\n\nfoo bla".lineColumn 1
#eval "ab\n\nfoo bla".lineColumn 2
#eval "ab\n\nfoo bla".lineColumn 3
#eval "ab\n\nfoo bla".lineColumn 8
#eval "ab\n\nfoo bla".lineColumn 100
