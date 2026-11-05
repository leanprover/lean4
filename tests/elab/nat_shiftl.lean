/-!
Tests kernel reduction of `Nat.shiftLeft` literals around the boundary between small (scalar)
and big `Nat`s, including shift amounts that do not fit in a machine word.
-/

example : (0 : Nat) <<< 0 = 0 := rfl
example : (0 : Nat) <<< 1000000 = 0 := rfl
-- `0 <<< n` reduces even when `n` is far too large to shift by.
example : (0 : Nat) <<< (2 ^ 100) = 0 := rfl

example : (7 : Nat) <<< 4 = 112 := rfl
example : (1 : Nat) <<< 30 = 1073741824 := rfl
example : (1 : Nat) <<< 31 = 2147483648 := rfl
example : (1 : Nat) <<< 32 = 4294967296 := rfl
example : (1 : Nat) <<< 62 = 4611686018427387904 := rfl
example : (1 : Nat) <<< 63 = 9223372036854775808 := rfl
example : (1 : Nat) <<< 64 = 18446744073709551616 := rfl
example : (3 : Nat) <<< 61 = 6917529027641081856 := rfl
example : (3 : Nat) <<< 62 = 13835058055282163712 := rfl
example : (0x7fffffffffffffff : Nat) <<< 1 = 18446744073709551614 := rfl
example : (0xffffffffffffffff : Nat) <<< 64 = 340282366920938463444927863358058659840 := rfl

#eval (0 : Nat) <<< (2 ^ 100)
#eval [0, 1, 30, 31, 32, 62, 63, 64, 65].map fun b => (7 : Nat) <<< b
