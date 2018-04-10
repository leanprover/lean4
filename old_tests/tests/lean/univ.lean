--

definition id2 (A : Type*) (a : A) := a

#check id2 Type* nat

#check id2 Type* nat


#check id2 Type nat

#check id2 _ nat

#check id2 (Sort (_+1)) nat

#check id2 (Sort (0+1)) nat

#check id2 Type* (Type 1)

#check id2 (Type*) (Type 1)
