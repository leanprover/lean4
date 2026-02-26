/- The following definition should fail. -/
@[class] def Foo (n : Nat) : Prop := n > 2


def Bla (n : Nat) : Prop := n > 2

attribute [class] Bla
