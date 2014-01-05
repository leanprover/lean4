Import Int.
Import Real.
Variable f : Int -> Int -> Int
print forall a, f a a > 0
print forall a b, f a b > 0
Variable g : Int -> Real -> Int
print forall a b, g a b > 0
print forall a b, g a (f a b) > 0
SetOption pp::coercion true
print forall a b, g a (f a b) > 0
print fun a, a + 1
print fun a b, a + b
print fun (a b) (c : Int), a + c + b
-- The next example shows a limitation of the current elaborator.
-- The current elaborator resolves overloads before solving the implicit argument constraints.
-- So, it does not have enough information for deciding which overload to use.
print (fun a b, a + b) 10 20.
Variable x : Int
-- The following one works because the type of x is used to decide which + should be used
print fun a b, a + x + b