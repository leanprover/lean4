Variable f {A : Type} (a : A) {B : Type} : A -> B -> A
Variable g {A B : Type} (a : A) {C : Type} : B -> C -> C
Notation 100 _ ; _ ; _ : f
Notation 100 _ ; _ ; _ : g
Check 10 ; true ; false
Check 10 ; 10 ; true
SetOption pp::notation false
Check 10 ; true ; false
Check 10 ; 10 ; true
SetOption pp::implicit true
Check 10 ; true ; false
Check 10 ; 10 ; true
