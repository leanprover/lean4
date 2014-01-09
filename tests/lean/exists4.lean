variable N : Type
variables a b c : N
variables P : N -> N -> N -> Bool
axiom H3 : P a b c

theorem T1 : exists x y z : N, P x y z := @exists_intro N (fun x : N, exists y z : N, P x y z) a
                                              (@exists_intro N _ b
                                                 (@exists_intro N (fun z : N, P a b z) c H3))

theorem T2 : exists x y z : N, P x y z := exists_intro a (exists_intro b (exists_intro c H3))

theorem T3 : exists x y z : N, P x y z := exists_intro _ (exists_intro _ (exists_intro _ H3))

theorem T4 (H : P a a b) : exists x y z, P x y z := exists_intro _ (exists_intro _ (exists_intro _ H))

print environment 4