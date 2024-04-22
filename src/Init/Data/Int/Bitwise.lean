/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Init.Data.Int.Basic
import Init.Data.Nat.Bitwise.Basic

namespace Int

/-! ## bit operations -/

/--
Bitwise not

Interprets the integer as an infinite sequence of bits in two's complement
and complements each bit.
```
~~~(0:Int) = -1
~~~(1:Int) = -2
~~~(-1:Int) = 0
```
-/
protected def not : Int -> Int
  | Int.ofNat n => Int.negSucc n
  | Int.negSucc n => Int.ofNat n

instance : Complement Int := ⟨.not⟩

/--
Bitwise shift right.

Conceptually, this treats the integer as an infinite sequence of bits in two's
complement and shifts the value to the right.

```lean
( 0b0111:Int) >>> 1 =  0b0011
( 0b1000:Int) >>> 1 =  0b0100
(-0b1000:Int) >>> 1 = -0b0100
(-0b0111:Int) >>> 1 = -0b0100
```
-/
protected def shiftRight : Int → Nat → Int
  | Int.ofNat n, s => Int.ofNat (n >>> s)
  | Int.negSucc n, s => Int.negSucc (n >>> s)

instance : HShiftRight Int Nat Int := ⟨.shiftRight⟩

end Int
