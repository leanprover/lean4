import Int.
variable a : Int
variable P : Int -> Int -> Bool
axiom H : P a a
theorem T : exists x : Int, P a a := ExistsIntro a H.
print environment 1.