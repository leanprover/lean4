#eval ("abc" ++ "cde").length
#eval "abc".popBack
#eval "".popBack
#eval "abcd".popBack
#eval ("abcd".mkIterator.nextn 2).remainingToString
#eval ("abcd".mkIterator.nextn 2).prevToString
#eval ("abcd".mkIterator.nextn 10).remainingToString
#eval ("abcd".mkIterator.nextn 10).prevToString
#eval "foo.Lean".popnBack 5
#eval "foo.Lean".backn 5
#eval "αβγ".popBack
#eval "αβ".length
#eval ("αβcc".mkIterator.next.insert "_foo_").toString
#eval ("αβcc".mkIterator.next.next.insert "_foo_").toString
#eval ("αβcc".mkIterator.next.next.prev.insert "_foo_").toString
#eval ("αβcc".mkIterator.remaining)
#eval ("αβcc".mkIterator.next.remaining)
#eval ("αβcc".mkIterator.next.insert "αbcβ").remaining
#eval (("αβcc".mkIterator.next.insert "αbcβ").remove 2).remaining
#eval (("αβcc".mkIterator.next.insert "αbcβ").remove 2).prev.remaining
#eval ("αβcc".mkIterator.next.toEnd).remaining
#eval "αβcc".mkIterator.offset
#eval "αβcc".mkIterator.next.offset
#eval "αβcc".mkIterator.next.next.offset
#eval ("αβcc".mkIterator.next.setCurr 'a').offset
#eval ("αβcc".mkIterator.next.insert "αbc").offset
#eval ("αβcc".mkIterator.next.insert "αbc").remaining
#eval ("αβcc".mkIterator.insert "αbc").offset
#eval ("αβcc".mkIterator.next.insert "αbcβ").offset
#eval "αβcd".mkIterator.toEnd.offset
#eval "ab\n\nfoo bla".lineColumn 0
#eval "ab\n\nfoo bla".lineColumn 1
#eval "ab\n\nfoo bla".lineColumn 2
#eval "ab\n\nfoo bla".lineColumn 3
#eval "ab\n\nfoo bla".lineColumn 8
#eval "ab\n\nfoo bla".lineColumn 100
