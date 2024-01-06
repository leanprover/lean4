-- This confirms that Nat bitwise operations are implemented in kernel
-- without this each line reports "error: (kernel) deep recursion detected"

example : let x := 2^20; x &&& x = x := rfl
example : let x := 2^20; x ||| x = x := rfl
example : let x := 2^20; x ^^^ x = 0 := rfl
example : 0 >>> 2^20 = 0 := rfl
example : 0 <<< 2^20 = 0 := rfl
