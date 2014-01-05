Import Int.

print 10 = 20
Variable f : Int -> Int -> Int
Variable g : Int -> Int -> Int -> Int
Notation 10 _ ++ _ : f
Notation 10 _ ++ _ : g
SetOption pp::implicit true
SetOption pp::notation false
print (10 ++ 20)
print (10 ++ 20) 10
