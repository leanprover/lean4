Variable g : Pi A : Type, A -> A.
Variables a b : Int
(*
The following example demonstrates a limitation in the current elaborator.
The current elaborator decides overloads before filling holes.
The symbol '>' is overloaded. The possible overloads are:
    Nat::lt   Nat -> Nat -> Nat
    Int::lt   Int -> Int -> Int
    Real::lt  Real -> Real -> Real
The type of (g _ a) is not available when the overload is decided, and
0 has type Nat. Then, the overload resolver selects
    Nat::lt   Nat -> Nat -> Nat
Now, when we fill the holes, (g _ a) is elaborated to (g Int a) which
has type Int, and we fail.
If the hole elaborator and overload resolver are executed simultaneously,
we would get the fully elaborated term:

    Int::le (g Int a) (nat_to_int 0)
*)
Axiom H1 : g _ a > 0
(*
One workaround consists in manually providing the coercion.
*)
Axiom H1 : g _ a > (nat_to_int 0)
