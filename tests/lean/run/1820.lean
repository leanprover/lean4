def f (p : nat × nat) : nat × nat := {p with}

structure P (A : Type) extends prod A A :=
(third : A)

def g (s : P nat) : nat × nat := {s with}

example : g (P.mk (1, 2) 3) = (1, 2) :=
rfl

example : g ⟨⟨1, 2⟩, 3⟩ = (1, 2) :=
rfl
