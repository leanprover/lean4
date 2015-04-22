section
  parameters {A : Type} {B : Type}

  definition foo1 (a : A) (b : B) := a

  parameters (B) {A} -- Should not change the order of the parameters

  definition foo2 (a : A) (b : B) := a

  parameters {B} (A)

  definition foo3 (a : A) (b : B) := a

  parameters (A) (B)

  definition foo4 (a : A) (b : B) := a

end

check @foo1
check @foo2
check @foo3
check @foo4
