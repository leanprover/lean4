open nat

definition foo [unfold 1 3] (a : nat) (b : nat) (c :nat) : nat :=
(a + c) * b

example (c : nat) : c = 1 → foo 1 c 0 = foo 1 1 0 :=
begin
  intro h,
  esimp,
  state,
  subst c
end

example (b c : nat) : c = 1 → foo 1 c b = foo 1 1 b :=
begin
  intro h,
  esimp,  -- should not unfold foo
  state,
  subst c
end

example (b c : nat) : c = 1 → foo b c 0 = foo b 1 0 :=
begin
  intro h,
  esimp,  -- should not unfold foo
  state,
  subst c
end

example (b c : nat) : c = 1 → foo 1 c 1 = foo c 1 1 :=
begin
  intro h,
  esimp,  -- should fold only first foo
  state,
  subst c
end
