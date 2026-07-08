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

example : 0.1 + 0.2 != 0.3 := rfl
example : 9689081178615771e-325 + 2.225e-308 == 2.321890811786158e-308 := by decide +kernel
example : 12312.123124 + 0.0002321 = 12312.123356099999 := rfl
example : 12312000000000000000000000000.123124 + 0.0002321 == 1.2312e+28 := by decide +kernel
