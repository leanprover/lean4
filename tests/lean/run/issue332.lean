import logic.eq
variable {a : Type}

definition foo {A : Type} : A → A :=
begin
intro a, exact a
end
check @foo

example : foo 10 = (10:num) :=
rfl
