import hott.path
open path
definition foo (A : Type) : Type := Π (a : A), a ≈ a
definition thm : Π (A : Type), foo A :=
begin
  intros,
  apply idp
end
