import data.examples.vector
open vector

definition map {A B C : Type} (f : A → B → C) : Π {n}, vector A n → vector B n → vector C n
| map nil nil             := nil
| map (a :: va) (b :: vb) := f a b :: map va vb
