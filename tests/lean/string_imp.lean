#eval ("abc" ++ "cde").length
#eval "abc".pop_back
#eval "".pop_back
#eval "abcd".pop_back
#eval ("abcd".mk_iterator.nextn 2).remaining_to_string
#eval ("abcd".mk_iterator.nextn 2).prev_to_string
#eval ("abcd".mk_iterator.nextn 10).remaining_to_string
#eval ("abcd".mk_iterator.nextn 10).prev_to_string
#eval "foo.lean".popn_back 5
#eval "foo.lean".backn 5
#eval "αβγ".pop_back
#eval "αβ".length
#eval ("αβcc".mk_iterator.next.insert "_foo_").to_string
#eval ("αβcc".mk_iterator.next.next.insert "_foo_").to_string
#eval ("αβcc".mk_iterator.next.next.prev.insert "_foo_").to_string
#eval ("αβcc".mk_iterator.remaining)
#eval ("αβcc".mk_iterator.next.remaining)
#eval ("αβcc".mk_iterator.next.insert "αbcβ").remaining
#eval (("αβcc".mk_iterator.next.insert "αbcβ").remove 2).remaining
#eval (("αβcc".mk_iterator.next.insert "αbcβ").remove 2).prev.remaining
#eval ("αβcc".mk_iterator.next.to_end).remaining
#eval "αβcc".mk_iterator.offset
#eval "αβcc".mk_iterator.next.offset
#eval "αβcc".mk_iterator.next.next.offset
#eval ("αβcc".mk_iterator.next.set_curr 'a').offset
#eval ("αβcc".mk_iterator.next.insert "αbc").offset
#eval ("αβcc".mk_iterator.next.insert "αbc").remaining
#eval ("αβcc".mk_iterator.insert "αbc").offset
#eval ("αβcc".mk_iterator.next.insert "αbcβ").offset
#eval "αβcd".mk_iterator.to_end.offset
#eval "ab\n\nfoo bla".line_column 0
#eval "ab\n\nfoo bla".line_column 1
#eval "ab\n\nfoo bla".line_column 2
#eval "ab\n\nfoo bla".line_column 3
#eval "ab\n\nfoo bla".line_column 8
#eval "ab\n\nfoo bla".line_column 100
