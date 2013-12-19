Variable myeq : Pi (A : Type), A -> A -> Bool
Show myeq _ true false
Variable T : Type
Variable a : T
Check myeq _ true a
Variable myeq2 {A:Type} (a b : A) : Bool
Infix 50 === : myeq2
SetOption lean::pp::implicit true
Check true === a