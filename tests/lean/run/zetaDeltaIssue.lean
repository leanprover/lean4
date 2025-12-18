structure A where
  a : Nat
structure B extends A where
  b : Nat
  w : a = b
def x : A where a := 37
@[simp] theorem x_a : x.a = 37 := rfl

def y : B := { x with b := 37, w := by simp }
