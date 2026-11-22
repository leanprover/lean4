/-!
Tests evaluation of the deprecated `String.Iterator` operations, including `setCurr`, `prev`,
`remainingToString`, `hasNext` and `hasPrev` on non-ASCII strings.
-/

def h (s : String) : String :=
let it₁ := s.mkIterator;
let it₂ := it₁.next;
it₁.remainingToString ++ "-" ++ it₂.remainingToString

#eval "αβγ".mkIterator.1
#eval "αβγ".mkIterator.next.1
#eval "αβγ".mkIterator.next.next.1
#eval "αβγ".mkIterator.next.2
#eval "".mkIterator.curr
#eval ("αβγ".mkIterator.setCurr 'a').toString
#eval (("αβγ".mkIterator.setCurr 'a').next.setCurr 'b').toString
#eval ((("αβγ".mkIterator.setCurr 'a').next.setCurr 'b').next.setCurr 'c').toString
#eval ((("αβγ".mkIterator.setCurr 'a').next.setCurr 'b').prev.setCurr 'c').toString
#eval ("abc".mkIterator.setCurr '0').toString
#eval (("abc".mkIterator.setCurr '0').next.setCurr '1').toString
#eval ((("abc".mkIterator.setCurr '0').next.setCurr '1').next.setCurr '2').toString
#eval ((("abc".mkIterator.setCurr '0').next.setCurr '1').prev.setCurr '2').toString
#eval ("abc".mkIterator.setCurr (Char.ofNat 955)).toString
#eval h "abc"
#eval "abc".mkIterator.remainingToString
#eval "".mkIterator.hasNext
#eval "a".mkIterator.hasNext
#eval "a".mkIterator.next.hasNext
#eval "".mkIterator.hasPrev
#eval "a".mkIterator.next.hasPrev
#eval "αβ".mkIterator.next.hasPrev
#eval "αβ".mkIterator.next.prev.hasPrev
