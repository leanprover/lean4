lemma rw_wild_card :
forall (a b c a' b' c' : nat),
(0 + a) = a' ->
(0 + b) = b' ->
(0 + c) = c' ->
a' + b' + c' = a + b + c :=
begin
    intros,
    rewrite [add_comm, add_zero] at *,
    rewrite [a_1, a_2, a_3]
end
