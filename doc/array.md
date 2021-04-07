# Arrays

The `Array` type implements a *dynamic* (aka growable) array.
It is defined as
```lean
# namespace hidden
structure Array (α : Type u) where
  data : List α
# end hidden
```
but its execution time representation is optimized, and it is similar to C++ `std::vector<T>` and Rust `Vec<T>`.
The Lean type checker has no special support for reducing `Array`s.

You can create arrays in several ways. You can create a small array by listing consecutive values between
`#[` and `]` and separated by commas, as shown in the following examples.

```lean
#check #[1, 2, 3] -- Array Nat

#check #[] -- Array ?m
```

The type of the array elements is inferred from the literals used and must be consistent.
```lean
#check #["hello", "world"] -- Array String

-- The following is not valid
#check_failure #[10, "hello"]
```
Recall that the command `#check_failure <term>` only succeeds when the given term is not type correct.

To create an array of size `n` in which all the elements are initialized to some value `a`, use `mkArray`.
```lean
#eval mkArray 5 'a'
-- #['a', 'a', 'a', 'a', 'a']
```

## Accessing elements

You can access array elements by using brackets (`[` and `]`).
```lean
#eval #['a', 'b', 'c'][1]
-- 'b'

def getThird (xs : Array Nat) : Nat :=
  xs[2]

#eval getThird #[10, 20, 30, 40]
-- 30
```
The bracket operator is whitespace sensitive.
```lean
def f (xs : List Nat) : List Nat :=
  xs ++ xs

def as : Array Nat :=
  #[1, 2, 3, 4]

#eval f [1, 2, 3] -- This is a function application

#eval as[2] -- This is an array access
```
