(* Define a "fake" type to simulate the natural numbers. This is just a test. *)
Variable N : Type
Variable lt : N -> N -> Bool
Variable zero : N
Variable one : N
Variable two : N
Variable three : N
Infix 50 < : lt
Axiom two_lt_three : two < three
Definition vector (A : Type) (n : N) : Type := Pi (i : N) (H : i < n), A
Definition const {A : Type} (n : N) (d : A) : vector A n := fun (i : N) (H : i < n), d
Definition update {A : Type} {n : N} (v : vector A n) (i : N) (d : A) : vector A n := fun (j : N) (H : j < n), if (j = i) d (v j H)
Definition select {A : Type} {n : N} (v : vector A n) (i : N) (H : i < n) : A := v i H
Definition map {A B C : Type} {n : N} (f : A -> B -> C) (v1 : vector A n) (v2 : vector B n) : vector C n := fun (i : N) (H : i < n), f (v1 i H) (v2 i H)
Show Environment 10
Check select (update (const three false) two true) two two_lt_three
Eval select (update (const three false) two true) two two_lt_three
Check update (const three false) two true
Echo "\n--------"
Check @select
Echo "\nmap type ---> "
Check @map
Echo "\nmap normal form --> "
Eval @map
Echo "\nupdate normal form --> "
Eval @update
