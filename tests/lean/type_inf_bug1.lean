import cast
set::option pp::colors false

check fun (A A': TypeM)
          (a   : A)
          (b   : A')
          (L2  : A' == A),
   let b' : A        := cast     L2 b,
       L3 : b == b'  := cast::eq L2 b
   in L3

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
    let L1 : A  == A'                             := type::eq H3,
        L2 : A' == A                              := symm L1,
        b' : A                                    := cast L2 b,
        L3 : b  == b'                             := cast::eq L2 b,
        L4 : a == b'                              := htrans H3 L3,
        L5 : f a == f b'                          := congr2 f L4,
        S1 : (forall x : A', B' x) == (forall x : A, B x) := symm H1,
        g' : (forall x : A, B x)                      := cast S1 g,
        L6 : g == g'                              := cast::eq S1 g,
        L7 : f == g'                              := htrans H2 L6,
        L8 : f b' == g' b'                        := congr1 b' L7,
        L9 : f a == g' b'                         := htrans L5 L8
    in L9
