theorem foo1 : 0 = (0:num) :=
rfl

theorem foo2 : 0 = (0:num) :=
rfl

theorem foo3 : 0 = (0:num) :=
foo2

definition foo4 : 0 = (0:num) :=
eq.trans foo2 foo1

print axioms foo4
print "------"
print axioms
print "------"
print foo3
