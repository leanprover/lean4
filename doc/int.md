# Integers

The `Int` type represents the arbitrary-precision integers. There are no overflows.
```lean
#eval (100000000000000000 : Int) * 200000000000000000000 * 1000000000000000000000
```
Recall that nonnegative numerals are considered to be a `Nat` if there are no typing constraints.
```lean
#check 1 -- Nat
#check -1 -- Int
#check (1:Int) -- Int
```

The function `Int.tdiv` implements integer division.
(As there are several rounding conventions for integer division,
Lean 4 itself does not provide a default instance for the `/` notation.)
```lean
#eval Int.tdiv (-10) 4 -- -2
```

Similar to `Nat`, the internal representation of `Int` is optimized. Small integers are
represented by a single machine word. Big integers are implemented using [GMP](https://gmplib.org/manual/) numbers.
We recommend you use fixed precision numeric types only in performance critical code.

The Lean kernel does not have special support for reducing `Int` during type checking.
However, since `Int` is defined as
```lean
# namespace hidden
inductive Int : Type where
  | ofNat   : Nat → Int
  | negSucc : Nat → Int
# end hidden
```
the type checker will be able reduce `Int` expressions efficiently by relying on the special support for `Nat`.

```lean
theorem ex : -2000000000 * 1000000000 = -2000000000000000000 :=
 rfl
```
