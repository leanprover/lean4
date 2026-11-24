/-!
Tests evaluation of basic `String` and `Substring.Raw` operations, including non-ASCII characters
and embedded null characters.
-/

def f (s : String) : String :=
s ++ " " ++ s

def g (s : String) : String :=
s.push ' ' ++ s.push '-'

#eval "hello" ++ "hello"
#eval f "hello"
#eval (f "αβ").length
#eval "hello".toList
#eval "αβ".toList
#eval "".toList
#eval "αβγ".toList
#eval "αβ".toList
#eval "αβ".push 'a'
#eval g "α"
#eval ("a".push (Char.ofNat 0)) ++ "bb"
#eval (("a".push (Char.ofNat 0)) ++ "αb").length
#eval "abc" == "abc"
#eval "abc" == "abd"
#eval "αβγ".drop 1 |>.copy
#eval "αβγ".takeEnd 1 |>.copy

def ss : Substring.Raw := "0123abcdαβγδ".toRawSubstring
#eval ss.drop 4 |>.takeRight 4
#eval ss.drop 4 |>.take 4
#eval ss.dropRight 4 |>.takeRight 4

def ssDots : Substring.Raw := "____abc.αβγ.123.____".toRawSubstring.extract ⟨4⟩ ⟨19⟩
#eval ssDots.splitOn "."
def ssHyphs : Substring.Raw := "____abc--αβγ--123--____".toRawSubstring.extract ⟨4⟩ ⟨22⟩
#eval ssHyphs.splitOn "--"

#eval String.Pos.Raw.get' "αβγ" 0 (by decide)
#eval String.Pos.Raw.get' "αβγ" ⟨2⟩ (by decide)
#eval String.Pos.Raw.next' "αβγ" ⟨2⟩ (by decide)
