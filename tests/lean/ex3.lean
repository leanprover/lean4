variable myeq : Pi (A : Type), A -> A -> Bool
print myeq _ true false
variable T : Type
variable a : T
check myeq _ true a
variable myeq2 {A:Type} (a b : A) : Bool
infix 50 === : myeq2
setoption lean::pp::implicit true
check true === a