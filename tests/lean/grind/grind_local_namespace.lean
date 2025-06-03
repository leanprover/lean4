def X : List Nat := [1, 2, 3]
def Y : List Nat := [1, 2, 3]

@[local grind] theorem A.foo : X.take 2 = Y.take 2 := rfl

example : X.take 2 = Y.take 2 := by grind -- fails, despite the `local grind` attribute

attribute [local grind] A.foo

example : X.take 2 = Y.take 2 := by grind -- but succeeds now

-- Everything works as expected if `foo` is not in a namespace:

@[local grind] theorem bar : X.take 1 = Y.take 1 := rfl

example : X.take 1 = Y.take 1 := by grind
