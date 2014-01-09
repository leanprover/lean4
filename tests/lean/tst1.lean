import if_then_else
-- Define a "fake" type to simulate the natural numbers. This is just a test.
variable N : Type
variable lt : N -> N -> Bool
variable zero : N
variable one : N
variable two : N
variable three : N
infix 50 < : lt
axiom two_lt_three : two < three
definition vector (A : Type) (n : N) : Type := forall (i : N) (H : i < n), A
definition const {A : Type} (n : N) (d : A) : vector A n := fun (i : N) (H : i < n), d
definition update {A : Type} {n : N} (v : vector A n) (i : N) (d : A) : vector A n := fun (j : N) (H : j < n), if (j = i) then d else (v j H)
definition select {A : Type} {n : N} (v : vector A n) (i : N) (H : i < n) : A := v i H
definition map {A B C : Type} {n : N} (f : A -> B -> C) (v1 : vector A n) (v2 : vector B n) : vector C n := fun (i : N) (H : i < n), f (v1 i H) (v2 i H)
print environment 10
check select (update (const three false) two true) two two_lt_three
eval select (update (const three false) two true) two two_lt_three
check update (const three false) two true
print "\n--------"
check @select
print "\nmap type ---> "
check @map
print "\nmap normal form --> "
eval @map
print "\nupdate normal form --> "
eval @update
