Show 10 = 20
Variable f : Int -> Int -> Int
Variable g : Int -> Int -> Int -> Int
Notation 10 _ ++ _ : f
Notation 10 _ ++ _ : g
Set pp::implicit true
Set pp::notation false
Show (10 ++ 20)
Show (10 ++ 20) 10
