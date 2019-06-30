def check (b : Bool) : IO Unit :=
unless b $ IO.println "failed"


def main : IO Unit :=
let a1 := [2, 3, 5].toArray in
let a2 := [4, 7, 9].toArray in
let a3 := [4, 7, 8].toArray in
do
 check (Array.isEqv a1 a2 (λ v w, v % 2 == w % 2));
 check (!Array.isEqv a1 a3 (λ v w, v % 2 == w % 2));
 check (a1 ++ a2 == [2, 3, 5, 4, 7, 9].toArray);
 check (a1.any (>4));
 check (!a1.any (>10));
 check (a1.all (<10))
