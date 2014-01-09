import Int.

print
let b := true,
    a : Int := b
in a

variable vector : Type -> Nat -> Type
variable const {A : Type} (n : Nat) (a : A) : vector A n

check
let a  := 10,
    v1 := const a true,
    v2 := v1
in v2

print
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Bool a := v1
in v2

check
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Bool a := v1
in v2

check
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Int  a := v1
in v2

variable foo : (vector Bool 10) -> (vector Int 10)
coercion foo

check
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Int  a := v1
in v2

set_option pp::coercion true

print
let a  := 10,
    v1 : vector Bool a := const a true,
    v2 : vector Int  a := v1
in v2
