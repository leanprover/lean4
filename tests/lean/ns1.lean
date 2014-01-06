import Int.

namespace foo.
  variable a : Nat.
  definition b := a.
  theorem T : a = b := refl a.
  axiom H : b >= a.
  namespace bla.
     variables a c d : Int.
     check a + b + c.
  end.
end.

check foo::T.
check foo::H.
check foo::a.
check foo::bla::a.

end