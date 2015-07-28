import data.nat
open nat

example (a b : nat) : a = succ b → a = b + 1 :=
begin
  intro h,
  try (unfold succ at h),
  unfold succ at h
end
