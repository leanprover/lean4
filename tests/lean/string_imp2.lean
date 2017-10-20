def f (s : string) : string :=
s ++ " " ++ s

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
