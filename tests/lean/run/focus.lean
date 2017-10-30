open nat
example (n m : ℕ) : n + m = m + n :=
begin
  induction m with m IHm,
  focus { induction n with n IHn,
    focus { reflexivity },
    focus { exact congr_arg succ IHn }},
  focus { apply eq.trans (congr_arg succ IHm),
    clear IHm, induction n with n IHn,
    focus { reflexivity },
    focus { exact congr_arg succ IHn }}
end