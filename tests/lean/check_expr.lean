import data.list
open sigma list

theorem foo (A : Type) (l : list A): A → A → list A :=
begin
  intros [a, b],
  check_expr (a::l),
end
