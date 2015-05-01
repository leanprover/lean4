variables {P Q R : Prop}
theorem foo (H : P → Q → R) (x : P) : Q → R :=
begin
  apply H,
  exact x
end
