/-!
Checks that small concrete `Float.Model` computations reduce definitionally (`rfl`).
-/

def pointOne : Float.Model := .ofBits 0x3FB999999999999A
def pointTwo : Float.Model := .ofBits 0x3FC999999999999A
def pointThree : Float.Model := .ofBits 0x3FD3333333333333

example : pointOne + pointTwo != pointThree := rfl

example : Float.Model.ofNat 1 + Float.Model.ofNat 1 = Float.Model.ofNat 2 := by rfl
example : Float.Model.ofNat 16 * Float.Model.ofNat 9 = Float.Model.ofNat 144 := by rfl
example : Float.Model.ofNat 16 * Float.Model.ofNat 9 == Float.Model.ofNat 144 := by rfl
