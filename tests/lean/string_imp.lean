
#eval ("abc" ++ "cde").length
#eval ("abcd".mkIterator.nextn 2).remainingToString
#eval ("abcd".mkIterator.nextn 10).remainingToString
#eval "αβ".length
#eval "αβcc".mkIterator.pos
#eval "αβcc".mkIterator.next.pos
#eval "αβcc".mkIterator.next.next.pos
#eval "αβcc".mkIterator.next.setCurr 'a'
#eval "αβcd".mkIterator.toEnd.pos
