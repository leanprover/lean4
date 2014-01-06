variable f {A : Type} (a : A) {B : Type} : A -> B -> A
variable g {A B : Type} (a : A) {C : Type} : B -> C -> C
notation 100 _ ; _ ; _ : f
notation 100 _ ; _ ; _ : g
check 10 ; true ; false
check 10 ; 10 ; true
set::option pp::notation false
check 10 ; true ; false
check 10 ; 10 ; true
set::option pp::implicit true
check 10 ; true ; false
check 10 ; 10 ; true
