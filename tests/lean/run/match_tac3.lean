import data.nat
open nat algebra

theorem tst (a b : nat) (H : a = 0) : a + b = b :=
begin
  revert H,
  match a with
  | zero  := λ H, by krewrite zero_add
  | (n+1) := λ H, nat.no_confusion H
  end
end

reveal tst
print definition tst
