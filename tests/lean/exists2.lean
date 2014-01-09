import Int.
variable a : Int
variable P : Int -> Int -> Bool
variable f : Int -> Int -> Int
variable g : Int -> Int
axiom H1 : P (f a (g a)) (f a (g a))
axiom H2 : P (f (g a) (g a)) (f (g a) (g a))
axiom H3 : P (f (g a) (g a)) (g a)
theorem T1 : exists x y : Int, P (f y x) (f y x) := exists_intro _ (exists_intro _ H1)
theorem T2 : exists x : Int, P (f x (g x)) (f x (g x)) := exists_intro _ H1
theorem T3 : exists x : Int, P (f x x) (f x x) := exists_intro _ H2
theorem T4 : exists x : Int, P (f (g a) x) (f x x) := exists_intro _ H2
theorem T5 : exists x : Int, P x x := exists_intro _ H2
theorem T6 : exists x y : Int, P x y := exists_intro _ (exists_intro _ H3)
theorem T7 : exists x : Int, P (f x x) x := exists_intro _ H3
theorem T8 : exists x y : Int, P (f x x) y := exists_intro _ (exists_intro _ H3)

print environment 8.