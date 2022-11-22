def f (s : String) : String :=
s ++ " " ++ s

def g (s : String) : String :=
s.push ' ' ++ s.push '-'

def h (s : String) : String :=
let it₁ := s.mkIterator;
let it₂ := it₁.next;
it₁.remainingToString ++ "-" ++ it₂.remainingToString

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
#eval "".mkIterator.hasNext
#eval "a".mkIterator.hasNext
#eval "a".mkIterator.next.hasNext
#eval "".mkIterator.hasPrev
#eval "a".mkIterator.next.hasPrev
#eval "αβ".mkIterator.next.hasPrev
#eval "αβ".mkIterator.next.prev.hasPrev
#eval "abc" == "abc"
#eval "abc" == "abd"
#eval "αβγ".drop 1
#eval "αβγ".takeRight 1

def ss : Substring := "0123abcdαβγδ".toSubstring
#eval ss.drop 4 |>.takeRight 4
#eval ss.drop 4 |>.take 4
#eval ss.dropRight 4 |>.takeRight 4

def ssDots : Substring := "____abc.αβγ.123.____".toSubstring.extract ⟨4⟩ ⟨19⟩
#eval ssDots.splitOn "."
def ssHyphs : Substring := "____abc--αβγ--123--____".toSubstring.extract ⟨4⟩ ⟨22⟩
#eval ssHyphs.splitOn "--"

#eval "αβγ".get' 0 (by decide)
#eval "αβγ".get' ⟨2⟩ (by decide)
#eval "αβγ".next' ⟨2⟩ (by decide)
