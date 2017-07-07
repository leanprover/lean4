example (a b c : nat) : a = 0 → b = 1 → c = 0 → b + a + c = b :=
begin
  intros,
  repeat {subst ‹_ = 0›}, -- substitute all equalities of the form `_ = 0`
  guard_target b + 0 + 0 = b,
  reflexivity
end
