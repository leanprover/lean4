import cast
set_option pp::colors false

check fun (A A': TypeM)
          (B   : A -> TypeM)
          (B'  : A' -> TypeM)
          (f   : forall x : A, B x)
          (g   : forall x : A', B' x)
          (a   : A)
          (b   : A')
          (H2  : f == g)
          (H3  : a == b),
     hcongr H2 H3
