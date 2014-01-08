import cast
set::option pp::colors false
universe M >= 1
universe U >= M + 1
definition TypeM := (Type M)

check fun (A A': TypeM)
          (B   : A -> TypeM)
          (B'  : A' -> TypeM)
          (f   : forall x : A, B x)
          (g   : forall x : A', B' x)
          (a   : A)
          (b   : A')
          (H1  : (forall x : A, B x) == (forall x : A', B' x))
          (H2  : f == g)
          (H3  : a == b),
    let
        S1 : (forall x : A', B' x) == (forall x : A, B x) := symm H1,
        L2 : A' == A                              := dominj S1,
        b' : A                                    := cast L2 b,
        L3 : b  == b'                             := cast::eq L2 b,
        L4 : a == b'                              := htrans H3 L3,
        L5 : f a == f b'                          := congr2 f L4,
        g' : (forall x : A, B x)                      := cast S1 g,
        L6 : g == g'                              := cast::eq S1 g,
        L7 : f == g'                              := htrans H2 L6,
        L8 : f b' == g' b'                        := congr1 b' L7,
        L9 : f a == g' b'                         := htrans L5 L8,
        L10 : g' b' == g b                        := cast::app S1 L2 g b
    in htrans L9 L10
