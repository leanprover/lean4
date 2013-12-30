Import int.
Variable a : Int
Variable P : Int -> Int -> Bool
Variable f : Int -> Int -> Int
Variable g : Int -> Int
Axiom H1 : P (f a (g a)) (f a (g a))
Axiom H2 : P (f (g a) (g a)) (f (g a) (g a))
Axiom H3 : P (f (g a) (g a)) (g a)
Theorem T1 : exists x y : Int, P (f y x) (f y x) := ExistsIntro _ (ExistsIntro _ H1)
Theorem T2 : exists x : Int, P (f x (g x)) (f x (g x)) := ExistsIntro _ H1
Theorem T3 : exists x : Int, P (f x x) (f x x) := ExistsIntro _ H2
Theorem T4 : exists x : Int, P (f (g a) x) (f x x) := ExistsIntro _ H2
Theorem T5 : exists x : Int, P x x := ExistsIntro _ H2
Theorem T6 : exists x y : Int, P x y := ExistsIntro _ (ExistsIntro _ H3)
Theorem T7 : exists x : Int, P (f x x) x := ExistsIntro _ H3
Theorem T8 : exists x y : Int, P (f x x) y := ExistsIntro _ (ExistsIntro _ H3)

Show Environment 8.