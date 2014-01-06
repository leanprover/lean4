variable N : Type
variables a b c : N
variables P : N -> N -> N -> Bool

theorem T1 (f : N -> N) (H : P (f a) b (f (f c))) : exists x y z, P x y z := exists::intro _ (exists::intro _ (exists::intro _ H))

print environment 1.
