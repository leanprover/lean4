Variable N : Type
Variables a b c : N
Variables P : N -> N -> N -> Bool

Theorem T1 (f : N -> N) (H : P (f a) b (f (f c))) : exists x y z, P x y z := ExistsIntro _ (ExistsIntro _ (ExistsIntro _ H))

print Environment 1.
