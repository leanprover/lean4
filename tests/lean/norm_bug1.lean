Import cast
SetOption pp::colors false

Definition TypeM := (Type M)
Definition TypeU := (Type U)

Check fun (A A': TypeM)
          (a   : A)
          (b   : A')
          (L2  : A' == A),
   let b' : A        := cast   L2 b,
       L3 : b == b'  := CastEq L2 b
   in L3

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
    let L1 : A  == A'               := DomInj H1,
        L2 : A' == A                := Symm L1,
        b' : A                      := cast L2 b,
        L3 : b  == b'               := CastEq L2 b,
        L4 : a == b'                := HTrans H3 L3,
        L5 : f a == f b'            := Congr2 f L4
    in L5
