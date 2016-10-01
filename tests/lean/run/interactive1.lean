def f : nat → nat := λ a, a

@[simp] lemma f_def (a : nat) : f a = a :=
rfl

def g : nat → nat := λ a, 1 + a

lemma g_def (a : nat) : g a = 1 + a :=
rfl

example (a b c : nat) : b = 0 → c = 1 → a + b + f c = g (f a) :=
begin
  intros h1 h2,
  simp [h1, h2, g_def, nat.add_comm 1 a]
end

example (b c : nat) : b = 0 → c = b + 1 → c = 1 :=
begin
  intros h1 h2,
  simp [h1] at h2,
  assumption
end

open nat

example (b c : nat) : succ b = succ c → b + 2 = c + 2 :=
begin
  intro h,
  injection h with h', clear h,
  trace_state,
  subst h'
end
