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

To create an array from a range of numbers use `List.range` and convert the result to an Array:

```lean
#eval (List.range 5).toArray
-- #[0, 1, 2, 3, 4]
```

## Accessing elements

You can access array elements by using brackets (`[` and `]`).
```lean
def f (a : Array Nat) (i : Fin a.size) :=
  a[i] + a[i]
```
Note that the index `i` has type `Fin a.size`, i.e., it is natural number less than `a.size`.
You can also write
```lean
def f (a : Array Nat) (i : Nat) (h  : i < a.size) :=
  a[i] + a[i]
```
The bracket operator is whitespace sensitive.

```lean
def f (xs : List Nat) : List Nat :=
  xs ++ xs

def as : Array Nat :=
  #[1, 2, 3, 4]

def idx : Fin 4 :=
  2

#eval f [1, 2, 3] -- This is a function application

#eval as[idx] -- This is an array access
```

Note that `[1, 2, 3]` is the syntax for building a `List`, so here we are passing
a list to the function `f`.  See [Lists](list.md).

The notation `a[i]` has two variants: `a[i]!` and `a[i]?`. In both cases, `i` has type `Nat`. The first one
produces a panic error message if the index `i` is out of bounds. The latter returns an `Option` type.

```lean
#eval #['a', 'b', 'c'][1]?
-- some 'b'
#eval #['a', 'b', 'c'][5]?
-- none
#eval #['a', 'b', 'c'][1]!
-- 'b'
```

## Concatenation

You can push a new item to the end of an array:
```lean
#eval #[1, 2, 3].push 7
-- #[1, 2, 3, 7]
```

And you can pop an item off the end of an array:


```lean
#eval #[1, 2, 3].pop
-- #[1, 2]
```

And you can append two arrays using the `++` operator:

```lean
#eval #[1, 2, 3] ++ (Array.mkArray 3 5)
-- #[1, 2, 3, 5, 5, 5]
```
or the `append` method:

```lean
#eval #[10].append #[20]
-- #[10, 20]
```

You can create an array of arrays:

```lean
#check #[#[20, 21]] -- Array (Array Nat)

#eval #[#[12]].append #[#[20, 21]]
-- #[#[12], #[20, 21]]
```

## Mapping

Arrays support "mapping" where you apply a given function to all elements in the array:

```lean
#eval #[3, 4, 5].map (λ x => x + 1)
-- #[4, 5, 6]

def square_cap (x : Nat) :=
  if x < 10 then x * x else 100

#eval #[3, 4, 5, 20].map square_cap
-- #[9, 16, 25, 100]

#eval #[1,2,3].map (λ x => toString x)
-- #["1", "2", "3"]
```

## Aggregation

And you can aggregate boolean predicates over an array with:

```lean
#eval (Array.mkArray 5 6).all (λ x => x < 10)
-- true

#eval #["hello", "world"].any (λ x => x.isEmpty)
-- false
```