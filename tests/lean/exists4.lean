Variable N : Type
Variables a b c : N
Variables P : N -> N -> N -> Bool
Axiom H3 : P a b c

Theorem T1 : exists x y z : N, P x y z := @ExistsIntro N (fun x : N, exists y z : N, P x y z) a
                                              (@ExistsIntro N _ b
                                                 (@ExistsIntro N (fun z : N, P a b z) c H3))

Theorem T2 : exists x y z : N, P x y z := ExistsIntro a (ExistsIntro b (ExistsIntro c H3))

Theorem T3 : exists x y z : N, P x y z := ExistsIntro _ (ExistsIntro _ (ExistsIntro _ H3))

Theorem T4 (H : P a a b) : exists x y z, P x y z := ExistsIntro _ (ExistsIntro _ (ExistsIntro _ H))

Show Environment 4