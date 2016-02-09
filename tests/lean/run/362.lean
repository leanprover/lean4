variables {a : Type}

definition foo (A : Type) : A → A :=
begin
  intro a, assumption
end

set_option pp.universes true
check foo
