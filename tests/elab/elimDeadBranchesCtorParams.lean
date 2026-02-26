@[noinline]
def f (_ : Unit) : Prod Unit Unit :=
  Prod.mk ⟨⟩ ⟨⟩

@[noinline]
def g (a : Unit) : Prod (Prod Unit Unit) (Prod Unit Unit) :=
  Prod.mk (f a) (f a)

def h (a : Unit) : Prod Unit Unit :=
  match g a with
  | ⟨_, y⟩ => y
