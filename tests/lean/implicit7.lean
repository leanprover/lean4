(*
   TODO(Leo):
   Improve elaborator's performance on this example.
   The main problem is that we don't have any indexing technique
   for the elaborator.
*)
Variable f {A : Type} (a : A) {B : Type} : A -> B -> A
Variable g {A B : Type} (a : A) {C : Type} : B -> C -> C
Notation 100 _ ; _ ; _ : f
Notation 100 _ ; _ ; _ : g
Check 10 ; true ; false
Check 10 ; 10 ; true
Set pp::notation false
Check 10 ; true ; false
Check 10 ; 10 ; true
Set pp::implicit true
Check 10 ; true ; false
Check 10 ; 10 ; true
