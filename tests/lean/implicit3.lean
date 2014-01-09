import Int.

print 10 = 20
variable f : Int -> Int -> Int
variable g : Int -> Int -> Int -> Int
notation 10 _ ++ _ : f
notation 10 _ ++ _ : g
set_option pp::implicit true
set_option pp::notation false
print (10 ++ 20)
print (10 ++ 20) 10
