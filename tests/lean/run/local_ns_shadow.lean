#check λ (a b : nat) (heq : a = b), (heq.symm : b = a)

example : ∀ (a b : nat), a = b → b = a :=
begin
  exact λ (a b : nat) (heq : a = b), heq.symm
end

example : ∀ (a b : nat), a = b → b = a :=
begin
  intros a b heq,
  exact heq.symm
end

section
  parameter x : nat
  def foo.bla : nat × nat :=
  (x, x+1)

  def g : nat :=
  foo.bla.fst + foo.bla.snd
end

example : g 10 = 21 :=
rfl
