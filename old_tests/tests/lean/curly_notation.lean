#check ({1, 2, 3} : set nat)
#check ({1} : set nat)
#check ({} : set nat)

definition s1 : set nat := {1, 2+3, 3, 4}
#print s1

definition s2 : set char := {'a', 'b', 'c'}
#print s2

definition s3 : set string := {"hello", "world"}
#print s3

#check { a ∈ s1 | a > 1 }
#check { a in s1 | a > 1 }
set_option pp.unicode false
#check { a ∈ s1 | a > 2 }


definition a := 10

#check ({a, a} : set nat)
#check ({a, 1, a} : set nat)
#check ({a} : set nat)

#check { a // a > 0 }
