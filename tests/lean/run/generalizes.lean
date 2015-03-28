import logic

theorem tst (A B : Type) (a : A) (b : B) : a == b → b == a :=
begin
  generalizes [a, b, B],
  intros [B', b, a, H],
  apply (heq.symm H),
end
