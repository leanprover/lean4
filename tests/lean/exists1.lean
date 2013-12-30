Import int.
Variable a : Int
Variable P : Int -> Int -> Bool
Axiom H : P a a
Theorem T : exists x : Int, P a a := ExistsIntro a H.
Show Environment 1.