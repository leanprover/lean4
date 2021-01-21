# Option

The `Option` type is used for representing data that may be either present or absent.
For example, imagine that we want to implement a safer version of natural number division;
by default, natural number division by 0 gives 0 as the answer:

```lean
#eval 2 / 0  -- = 0
```

But perhaps we want a different answer for division by 0, one that is not a natural number,
to represent "undefined".
We can create our own natural number division function, and return an `Option`:

```lean
def safeDiv : Nat → Nat → Option Nat
  | m, 0 => none
  | m, n => some (m / n)
```

Returning `Option Nat` means our function could either return `none` (this represents undefined)
or `some` natural number.
We can test `safeDiv`:

```lean
#eval safeDiv 8 2  -- = some 4
#eval safeDiv 8 0  -- = none
```
