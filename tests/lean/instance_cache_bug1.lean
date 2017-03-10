constant A : Type
constant a : A
constant A_has_add : has_add A

#check a + a -- ERROR

attribute [instance] A_has_add

#check a + a
