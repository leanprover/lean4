def foo (a : nat) (b : nat) := b
def g (a : nat) := foo (1000000000000 + 1) a
def f (a : nat) := foo (1 + 1000000000000) a

lemma foo_lemma (a b : nat) : foo b a = foo (1 + 1000000000000) a :=
rfl

lemma f_fold_lemma (a : nat) : foo (1 + 1000000000000) a = f a :=
rfl

lemma ex (a : nat) (p : nat → Prop) (h : p (f a)) : p (g a) :=
begin
  simp only [g, foo_lemma, f_fold_lemma],
  exact h,
end
