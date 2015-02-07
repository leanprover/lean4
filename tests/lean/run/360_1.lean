structure is_tr [class] (A : Type) : Type :=
(x : A)

theorem foo (B : Type) [H : is_tr B] : B :=
sorry

theorem bar (A : Type) (H : is_tr A) : A :=
begin
  apply foo
end
