Import "cast.lean"
SetOption pp::colors false

Definition TypeM := (Type M)
Definition TypeU := (Type U)

Check fun (A A': TypeM)
          (B   : A -> TypeM)
          (B'  : A' -> TypeM)
          (f   : Pi x : A, B x)
          (g   : Pi x : A', B' x)
          (a   : A)
          (b   : A')
          (H1  : (Pi x : A, B x) == (Pi x : A', B' x))
          (H2  : f == g)
          (H3  : a == b),
    let
        S1 : (Pi x : A', B' x) == (Pi x : A, B x) := Symm H1,
        L2 : A' == A                              := DomInj S1,
        b' : A                                    := cast L2 b,
        L3 : b  == b'                             := CastEq L2 b,
        L4 : a == b'                              := HTrans H3 L3,
        L5 : f a == f b'                          := Congr2 f L4,
        g' : (Pi x : A, B x)                      := cast S1 g,
        L6 : g == g'                              := CastEq S1 g,
        L7 : f == g'                              := HTrans H2 L6,
        L8 : f b' == g' b'                        := Congr1 b' L7,
        L9 : f a == g' b'                         := HTrans L5 L8,
        L10 : g' b' == g b                        := CastApp S1 L2 g b
    in HTrans L9 L10
