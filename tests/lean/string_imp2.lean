def f (s : String) : String :=
s ++ " " ++ s

def g (s : String) : String :=
s.push ' ' ++ s.push '-'

def h (s : String) : String :=
let it₁ := s.mkIterator;
let it₂ := it₁.next;
it₁.remainingToString ++ "-" ++ it₂.remainingToString


#exit -- Disabled until we implement new VM

def r (s : String) : String :=
let it₁ := s.mkIterator.toEnd;
let it₂ := it₁.prev;
it₁.prevToString ++ "-" ++ it₂.prevToString

def s (s : String) : String :=
let it₁ := s.mkIterator.toEnd;
let it₂ := it₁.prev;
(it₁.insert "abc").toString ++ (it₂.insert "de").toString


#eval "hello" ++ "hello"
#eval f "hello"
#eval (f "αβ").length
#eval "hello".toList
#eval "αβ".toList
#eval "".toList
#eval "αβγ".toList
#eval "αβγ".mkIterator.1
#eval "αβγ".mkIterator.next.1
#eval "αβγ".mkIterator.next.next.1
#eval "αβγ".mkIterator.next.2
#eval "αβ".1
#eval "αβ".push 'a'
#eval g "α"
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
#eval ("a".push (Char.ofNat 0)) ++ "bb"
#eval (("a".push (Char.ofNat 0)) ++ "αb").length
#eval r "abc"
#eval "abc".mkIterator.toEnd.prevToString
#eval "".mkIterator.hasNext
#eval "a".mkIterator.hasNext
#eval "a".mkIterator.next.hasNext
#eval "".mkIterator.hasPrev
#eval "a".mkIterator.next.hasPrev
#eval "αβ".mkIterator.next.hasPrev
#eval "αβ".mkIterator.next.prev.hasPrev
#eval ("αβ".mkIterator.toEnd.insert "abc").toString
#eval ("αβ".mkIterator.next.insert "abc").toString
#eval s "αβ"
#eval ("abcdef".mkIterator.next.remove 2).toString
#eval ("abcdef".mkIterator.next.next.remove 2).toString
#eval ("abcdef".mkIterator.next.remove 3).toString
#eval (("abcdef".mkIterator.next.next.next.remove 100).prev.setCurr 'a').toString
#eval ("abcdef".mkIterator.next.next.next.remove 100).hasNext
#eval ("abcdef".mkIterator.next.next.next.remove 100).prev.hasNext
#eval toBool $ "abc" = "abc"
#eval toBool $ "abc" = "abd"
