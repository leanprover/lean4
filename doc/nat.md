# Natural numbers

The `Nat` type represents the natural numbers, i.e., arbitrary-precision unsigned integers.
There are no overflows.

```lean
#eval 100000000000000000 * 200000000000000000000 * 1000000000000000000000
```

A numeral is considered to be a `Nat` if there are no typing constraints.
```lean
#check 10    -- Nat
#check id 10 -- Nat

def f (x : Int) : Int :=
  x - 1

#eval f (3 - 5) -- 3 and 5 are `Int` since `f` expects an `Int`.
-- -3
```

The operator `-` for `Nat` implements truncated subtraction.
```lean
#eval 10 - 5 -- 5
#eval 5 - 10 -- 0

theorem ex : 5 - 10 = 0 :=
  rfl

#eval (5:Int) - 10 -- -5
```

The operator `/` for `Nat` implements Euclidean division.
```lean
#eval 10 / 4 -- 2

#check 10.0 / 4.0 -- Float
#eval 10.0 / 4.0  -- 2.5
```

As we described in the previous sections, we define the `Nat` type as an `inductive` datatype.
```lean
# namespace hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
# end hidden
```
However, the internal representation of `Nat` is optimized. Small natural numbers (i.e., < `2^63` in a 64-bit machine) are
represented by a single machine word. Big numbers are implemented using [GMP](https://gmplib.org/manual/) numbers.
We recommend you use fixed precision numeric types only in performance critical code.

The Lean kernel has builtin support for the `Nat` type too, and can efficiently reduce `Nat` expressions during type checking.
```lean
#reduce 100000000000000000 * 200000000000000000000 * 1000000000000000000000

theorem ex
      : 1000000000000000 * 2000000000000000000 = 2000000000000000000000000000000000 :=
  rfl
```
The sharp-eyed reader will notice that GMP is part of the Lean kernel trusted code base.
We believe this is not a problem because you can use external type checkers to double-check your developments,
and we consider GMP very trustworthy.
Existing external type checkers for Lean 3 (e.g., [Trepplein](https://github.com/gebner/trepplein) and [TC](https://github.com/leanprover/tc))
can be easily adapted to Lean 4.
If you are still concerned after checking your development with multiple different external checkers because
they may all rely on buggy arbitrary-precision libraries,
you can develop your own certified arbitrary-precision library and use it to implement your own type checker for Lean.
