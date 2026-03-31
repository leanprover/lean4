def Foo (n : Nat) : Prop := True
def aux := 1
nonrec def Foo.aux : Foo aux :=
  have h : aux = 1 := rfl
  trivial
