# List

A `List` looks similar to an [Array](Array.md) but it is a pure Lean inductive type that does not
have an optimized runtime other than what the Lean compiler builds from the List implementation.

```lean
# namespace hidden
inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α
# end hidden
```

A list then is defined recursively through concatenation of some `head` item with an existing `tail`
via the `cons` constructor.

## Literals

You can create lists in several ways. You can start with a small list by listing consecutive values between
`[` and `]` and separated by commas, as shown in the following examples.

```lean
#check [1, 2, 3] -- List Nat

#check #[1, 2, 3] -- Array Nat - arrays have a # prefix.

#check [] -- List ?m  -- unresolved type.
#check List.nil (α := String) -- List String - specify the type parameter

#eval List.cons "a" ["b", "c", "d"]     -- ["a", "b", "c", "d"]
```

Notice that Lean is able to infer the list element type in these cases, createing `List nat` and `List String`.

Notice also that `[]` is short hand for `List.nil` and that it is missing any list element type. To
resolve this you can write the following:

There is special syntax for `cons`, namely, `::` as follows:

```lean
#eval 0 :: [1, 2, 3]        -- [0, 1, 2, 3]
```

The type of the list elements is inferred from the literals used and must be consistent.
```lean
#check ["hello", "world"] -- List String

-- The following is not valid, the List element type must be homogeneous
#check_failure [10, "hello"]
```
Recall that the command `#check_failure <term>` only succeeds when the given term is not type correct.

You can also invoke type inference on empty lists using parens to type the expression:
```lean
#check ([] : List String) -- List String - use type inference
```

or by using a definition:

```lean
def emptyListOfStrings : List String := []

#check emptyListOfStrings -- List String
```

You can convert an Array to a List using `toList` :

```lean
#eval (Array.mkArray 5 'a').toList      -- ['a', 'a', 'a', 'a', 'a']
```

To create an list from a range of numbers use `List.range`:

```lean
#eval List.range 5      -- [0, 1, 2, 3, 4]
```

## Accessing elements

You can access list elements by using square brackets `[` and `]`.
```lean
#eval ['a', 'b', 'c'][1]        -- 'b'

def getThird (xs : List Nat) : Nat :=
  xs[2]!

#eval getThird [10, 20, 30, 40]     -- 30
```
Notice here we had to use an exclamation mark on `xs[2]!` in order to tell Lean that
index 2 is valid, since getThird has no idea what length the incoming list is.

The notation `a[i]` has two variants: `a[i]!` and `a[i]?`. In both cases, `i` has type `Nat`. The
first one produces a panic error message if the index `i` is out of bounds. The latter returns an
`Option` type.


```lean
#eval ['a', 'b', 'c'][1]?
-- some 'b'
#eval ['a', 'b', 'c'][5]?
-- none
#eval ['a', 'b', 'c'][1]!
-- 'b'
```

The bracket operator is whitespace sensitive.
```lean
def f (xs : List Nat) : List Nat :=
  xs.reverse

def as : List Nat :=
  List.range 4

#eval f [1, 2, 3] -- This is a function application

#eval as[2] -- This is an array access

#eval [1, 2, 3][2]  -- 3
```

## Concatenation

You can add a new item to the front of a list by constructing a new List using the `cons`
constructor:

```lean
#eval List.cons 7 [1, 2, 3]
-- [7, 1, 2, 3]
```

And you can pop an item off the front of a list using pattern matching:

```lean
def pop (x: List α) : List α :=
  match x with
  | .nil => .nil
  | head :: tail => tail

#eval pop [1,2,3]   -- [2, 3]
```

And you can append two lists using the `++` operator:

```lean
#eval [1, 2, 3] ++ (List.range 4) ++ [5, 6, 7]
-- [1, 2, 3, 0, 1, 2, 3, 5, 6, 7]
```
which is short hand for the `append` method:

```lean
#eval #eval List.append [1, 2, 3] (List.range 4)
-- [1, 2, 3, 0, 1, 2, 3]
```

You can create a list of lists:

```lean
#check [[20, 21]] -- List (List Nat)

#eval List.append [[12]] [[20, 21]]
-- [[12], [20, 21]]
```

## Mapping

Lists support "mapping" where you apply a given function to all elements in the list:

```lean
#eval List.map (λ x => x + 1) [3, 4, 5]
-- [4, 5, 6]

def square_cap (x : Nat) :=
  if x < 10 then x * x else 100

#eval List.map square_cap [3, 4, 5, 20]
-- [9, 16, 25, 100]

#eval List.map (λ x => toString x) [1,2,3]
-- ["1", "2", "3"]
```

Notice that map can change the List element type.  Map here is actually part of a bigger
story around Monads.  List is a Monad.

## Aggregation

And you can aggregate boolean predicates over a list with:

```lean
#eval List.all (List.range 5) (λ x => x < 10)
-- true

#eval List.any ["hello", "world"] (λ x => x.isEmpty)
-- false
```

