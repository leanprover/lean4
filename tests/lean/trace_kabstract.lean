set_option trace.rewrite true
set_option trace.kabstract true

example (f : nat → nat) (a b : nat) (h : f a = a) : f (f a) = a :=
begin
  rw h,
  rw h
end
