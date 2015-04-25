import data.nat
open nat

definition f (a b : nat) := a + b

example (a b : nat) : f a b = 0 → f b a = 0 :=
begin
  intro h,
  unfold f at h,
  state,
  unfold f,
  state,
  rewrite [add.comm],
  exact h
end

example (a b : nat) : f a b = 0 → f b a = 0 :=
begin
  intro h,
  unfold f at *,
  state,
  rewrite [add.comm],
  exact h
end

example (a b c : nat) : f c c = 0 → f a b = 0 → f b a = f c c :=
begin
  intros [h₁, h₂],
  unfold f at (h₁, h₂),
  state,
  unfold f,
  rewrite [add.comm, h₁, h₂],
end

example (a b c : nat) : f c c = 0 → f a b = 0 → f b a = f c c :=
begin
  intros [h₁, h₂],
  unfold f at * ⊢,
  state,
  unfold f,
  rewrite [add.comm, h₁, h₂],
end
