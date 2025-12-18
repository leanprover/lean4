-- This confirms that Nat bitwise operations are implemented in kernel
-- and performs a few basic tests.

-- Without kernel support the tests containing the 2^20 constant will
-- fail with "error: (kernel) deep recursion detected"

example : 0      &&& 0      = 0 := rfl
example : 0      &&& 0b1111 = 0 := rfl
example : 0b1111 &&& 0      = 0 := rfl
example : 0b1111 &&& 0b1111 = 0b1111 := rfl
example : 0b1100 &&& 0b1010 = 0b1000 := rfl
example : let x := 2^20; x &&& x = x := rfl

example : 0      ||| 0      = 0 := rfl
example : 0      ||| 0b1111 = 0b1111 := rfl
example : 0b1111 ||| 0      = 0b1111 := rfl
example : 0b1111 ||| 0b1111 = 0b1111 := rfl
example : 0b1100 ||| 0b1010 = 0b1110 := rfl
example : let x := 2^20; x ||| x = x := rfl

example : 0      ^^^ 0      = 0 := rfl
example : 0      ^^^ 0b1111 = 0b1111 := rfl
example : 0b1111 ^^^ 0      = 0b1111 := rfl
example : 0b1111 ^^^ 0b1111 = 0      := rfl
example : 0b1100 ^^^ 0b1010 = 0b0110 := rfl
example : 0b0110 ^^^ 0b0101 = 0b0011 := rfl
example : let x := 2^20; x ^^^ x = 0 := rfl

example : 0      >>> 0      = 0 := rfl
example : 0b1011 >>> 1      = 0b0101 := rfl
example : 0b1011 >>> 2      = 0b0010 := rfl
example : 0      >>> 2^20   = 0 := rfl

example : 0      <<< 0      = 0 := rfl
example : 0b1011 <<< 1      = 0b010110 := rfl
example : 0b1011 <<< 2      = 0b101100 := rfl
example : 0      <<< 2^20   = 0 := rfl
