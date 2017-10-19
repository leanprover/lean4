#eval ("abc" ++ "cde").length
#eval "abc".pop_back
#eval "".pop_back
#eval "abcd".pop_back
#eval ("abcd".mk_iterator.nextn 2).next_to_string
#eval ("abcd".mk_iterator.nextn 2).prev_to_string
#eval ("abcd".mk_iterator.nextn 10).next_to_string
#eval ("abcd".mk_iterator.nextn 10).prev_to_string
#eval "foo.lean".popn_back 5
#eval "foo.lean".backn 5
#eval "αβγ".pop_back
#eval "αβ".length
#eval ("αβcc".mk_iterator.next.insert "_foo_").to_string
#eval ("αβcc".mk_iterator.next.next.insert "_foo_").to_string
#eval ("αβcc".mk_iterator.next.next.prev.insert "_foo_").to_string
