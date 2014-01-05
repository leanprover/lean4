Import Int.

print
let b := true,
    a : Int := b
in a

Variable vector : Type -> Nat -> Type
Variable const {A : Type} (n : Nat) (a : A) : vector A n

Check
let a  := 10,
    v1 := const a true,
    v2 := v1
in v2

print
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Bool a := v1
in v2

Check
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Bool a := v1
in v2

Check
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Int  a := v1
in v2

Variable foo : (vector Bool 10) -> (vector Int 10)
Coercion foo

Check
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Int  a := v1
in v2

SetOption pp::coercion true

print
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Int  a := v1
in v2
