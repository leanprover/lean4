Import int.

Namespace foo.
  Variable a : Nat.
  Definition b := a.
  Theorem T : a = b := Refl a.
  Axiom H : b >= a.
  Namespace bla.
     Variables a c d : Int.
     Check a + b + c.
  EndNamespace.
EndNamespace.

Check foo::T.
Check foo::H.
Check foo::a.
Check foo::bla::a.

EndNamespace.