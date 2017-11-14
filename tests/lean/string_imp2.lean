def f (s : string) : string :=
s ++ " " ++ s

def g (s : string) : string :=
s.push ' ' ++ s.push '-'

def h (s : string) : string :=
let it₁ := s.mk_iterator in
let it₂ := it₁.next in
it₁.next_to_string ++ "-" ++ it₂.next_to_string

def r (s : string) : string :=
let it₁ := s.mk_iterator.to_end in
let it₂ := it₁.prev in
it₁.prev_to_string ++ "-" ++ it₂.prev_to_string

def s (s : string) : string :=
let it₁ := s.mk_iterator.to_end in
let it₂ := it₁.prev in
(it₁.insert "abc").to_string ++ (it₂.insert "de").to_string

#eval "hello" ++ "hello"
#eval f "hello"
#eval (f "αβ").length
#eval "hello".to_list
#eval "αβ".to_list
#eval "".to_list
#eval "αβγ".to_list
#eval "αβγ".fold [] (λ r c, c::r)
#eval "".fold 0 (λ r c, r+1)
#eval "αβγ".fold 0 (λ r c, r+1)
#eval "αβγ".mk_iterator.1
#eval "αβγ".mk_iterator.next.1
#eval "αβγ".mk_iterator.next.next.1
#eval "αβγ".mk_iterator.next.2
#eval "αβ".1
#eval string.empty
#eval "αβ".push 'a'
#eval g "α"
#eval "".mk_iterator.curr
#eval ("αβγ".mk_iterator.set_curr 'a').to_string
#eval (("αβγ".mk_iterator.set_curr 'a').next.set_curr 'b').to_string
#eval ((("αβγ".mk_iterator.set_curr 'a').next.set_curr 'b').next.set_curr 'c').to_string
#eval ((("αβγ".mk_iterator.set_curr 'a').next.set_curr 'b').prev.set_curr 'c').to_string
#eval ("abc".mk_iterator.set_curr '0').to_string
#eval (("abc".mk_iterator.set_curr '0').next.set_curr '1').to_string
#eval ((("abc".mk_iterator.set_curr '0').next.set_curr '1').next.set_curr '2').to_string
#eval ((("abc".mk_iterator.set_curr '0').next.set_curr '1').prev.set_curr '2').to_string
#eval ("abc".mk_iterator.set_curr (char.of_nat 955)).to_string
#eval h "abc"
#eval "abc".mk_iterator.next_to_string
#eval ("a".push (char.of_nat 0)) ++ "bb"
#eval (("a".push (char.of_nat 0)) ++ "αb").length
#eval r "abc"
#eval "abc".mk_iterator.to_end.prev_to_string
#eval "".mk_iterator.has_next
#eval "a".mk_iterator.has_next
#eval "a".mk_iterator.next.has_next
#eval "".mk_iterator.has_prev
#eval "a".mk_iterator.next.has_prev
#eval "αβ".mk_iterator.next.has_prev
#eval "αβ".mk_iterator.next.prev.has_prev
#eval ("αβ".mk_iterator.to_end.insert "abc").to_string
#eval ("αβ".mk_iterator.next.insert "abc").to_string
#eval s "αβ"
#eval ("abcdef".mk_iterator.next.remove 2).to_string
#eval ("abcdef".mk_iterator.next.next.remove 2).to_string
#eval ("abcdef".mk_iterator.next.remove 3).to_string
#eval (("abcdef".mk_iterator.next.next.next.remove 100).prev.set_curr 'a').to_string
#eval ("abcdef".mk_iterator.next.next.next.remove 100).has_next
#eval ("abcdef".mk_iterator.next.next.next.remove 100).prev.has_next
#eval to_bool $ "abc" = "abc"
#eval to_bool $ "abc" = "abd"
