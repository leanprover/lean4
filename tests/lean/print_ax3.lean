theorem foo1 : 0 = (0:nat) :=
rfl

theorem foo2 : 0 = (0:nat) :=
rfl

theorem foo3 : 0 = (0:nat) :=
foo2

definition foo4 : 0 = (0:nat) :=
eq.trans foo2 foo1

lemma foo5 : true = false :=
propext sorry

#print axioms foo4
#print "------"
#print axioms
#print "------"
#print foo3
#print "------"
#print axioms foo5
