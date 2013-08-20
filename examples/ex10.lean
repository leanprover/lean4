(* Define a "fake" type to simulate the natural numbers. This is just a test. *)
Variable Natural : Type
Variable lt : Natural -> Natural -> Bool
Variable zero : Natural
Variable one : Natural
Variable two : Natural
Variable three : Natural
Infix 50 < : lt
Axiom two_lt_three : two < three
Definition vector (A : Type) (n : Natural) : Type := Pi (i : Natural) (H : i < n), A
Definition const (A : Type) (n : Natural) (d : A) : vector A n := fun (i : Natural) (H : i < n), d
Definition update (A : Type) (n : Natural) (v : vector A n) (i : Natural) (d : A) : vector A n := fun (j : Natural) (H : j < n), if A (j = i) d (v j H)
Definition select (A : Type) (n : Natural) (v : vector A n) (i : Natural) (H : i < n) : A := v i H
Environment
Check select Bool three (update Bool three (const Bool three false) two true) two two_lt_three
Eval select Bool three (update Bool three (const Bool three false) two true) two two_lt_three
Check select


