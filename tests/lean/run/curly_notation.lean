check ({1, 2, 3} : set nat)
check ({1} : set nat)
check ({} : set nat)

definition s1 : set nat := {1, 2+3, 3, 4}
print s1

definition s2 : set char := {'a', 'b', 'c'}
print s2

definition s3 : set string := {"hello", "world"}
print s3
