def f (a : nat) (b : nat := a) (c : nat := a) :=
a + b + c

lemma ex1 (a a' b c d : nat) (h : b = c) (h2 : a = a') : f a b d = f a' c d :=
by cc

lemma ex2 (a a' b c d : nat) (h : b = c) (h2 : a = a') : f a b d = f a' c d :=
by rw [h, h2]

set_option pp.beta true
set_option pp.all true

lemma ex3 (a a' b c d : nat) (h : b = c) (h2 : a = a') : f a b d = f a' c d :=
begin
  simp [h, h2],
end

open tactic

run_command mk_const `f >>= get_fun_info >>= trace
run_command mk_const `eq >>= get_fun_info >>= trace
run_command mk_const `id >>= get_fun_info >>= trace

set_option trace.congr_lemma true
set_option trace.app_builder true

run_command mk_const `f >>= mk_congr_lemma_simp >>= (λ l, trace l^.type)
