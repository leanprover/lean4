# List

A `List` is a container of elements of a given type, similar to linked lists in other
languages.

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

Notice that Lean is able to infer the list element type in these cases, creating `List Nat` and `List String`.

Notice also that `[]` is short hand for `List.nil` and that it cannot infer any implicit list element type.

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

**Note**: Accessing elements this way is not recommended because it can lead to quadratic
performance if you write code like this:

```lean
def badLoop (x: List Nat) : String := Id.run do
  for i in [0:x.length] do
    if x[i]! == 99 then
      return "found it"
    else
      continue
  return "not found"

#eval badLoop (List.range 100) -- performs 99 * 99 list iterations!
```

So in this case it is much better to use `find?` or `indexOf?` or `replace`
or `erase`, or whatever the operation is you are trying to do on the found element.

## Concatenation

You can add a new item to the front of a list by constructing a new List using the `cons`
constructor:

```lean
#eval 7 :: [1, 2, 3]
-- [7, 1, 2, 3]
```

And you can append two lists using the `++` operator:

```lean
#eval [1, 2, 3] ++ (List.range 4) ++ [5, 6, 7]
-- [1, 2, 3, 0, 1, 2, 3, 5, 6, 7]
```
which is short hand for the `append` method:

```lean
#eval [1, 2, 3].append (List.range 4)
-- [1, 2, 3, 0, 1, 2, 3]
```

You can create a list of lists:

```lean
#check [[20, 21]] -- List (List Nat)

#eval [[12]].append [[20, 21]]
-- [[12], [20, 21]]
```

## Manipulating

You can pop some elements off the front of a list

```lean
#eval [1,2,3].take 2   -- [1, 2]
```

And you can drop some items off the front and get the remainder:

```lean
#eval [1,2,3].drop 1   -- [2, 3]
```

You can also erase the first matching item:

```lean
#eval ["a", "b", "c", "b"].erase "b" -- ["a", "c", "b"]
```

Or you can remove all matching items:

```lean
#eval ["a", "b", "c", "b"].removeAll ["b", "c"] -- ["a"]
```

## Mapping

Lists support "mapping" where you apply a given function to all elements in the list:

```lean
#eval [3, 4, 5].map (λ x => x + 1)
-- [4, 5, 6]

def square_cap (x : Nat) :=
  if x < 10 then x * x else 100

#eval [3, 4, 5, 20].map square_cap
-- [9, 16, 25, 100]

#eval [1,2,3].map (λ x => toString x)
-- ["1", "2", "3"]
```

Notice that map can change the List element type.  Map here is actually part of a bigger
story around Functors.  List is a Functor and all Functors have a `map` method.

## Aggregation

And you can aggregate boolean predicates over a list with:

```lean
#eval (List.range 5).all (λ x => x < 10)
-- true

#eval ["hello", "world"].any (λ x => x.isEmpty)
-- false
```

## Conversion

You can convert a list to an array and vice versa:

```lean
#eval ["a", "b", "c", "b"].toArray -- #["a", "b", "c", "b"]

#eval #["a", "b", "c", "b"].toList -- ["a", "b", "c", "b"]
```