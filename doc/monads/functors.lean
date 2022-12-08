/-!
# Functor

A `Functor` is any type that can act as a generic container that allows you to transform the
underlying values inside the container using a function, so that the values are all updated, but the
structure of the container is the same. This is called "mapping".

A List is one of the most basic examples of a `Functor`.

A list contains zero or more elements of the same, underlying type.  When you `map` a function over
a list, you create a new list with the same number of elements, where each has been transformed by
the function:
-/
#eval List.map (λ x => toString x) [1,2,3] -- ["1", "2", "3"]

-- you can also write this using dot notation on the List object
#eval [1,2,3].map (λ x => toString x)  -- ["1", "2", "3"]

/-!
Here we converted a list of natural numbers (Nat) to a list of strings where the lambda function
here used `toString` to do the transformation of each element. Notice that when you apply `map` the
"structure" of the object remains the same, in this case the result is always a `List` of the same
size.

Note that in Lean a lambda function can be written using `fun` keyword or the unicode
symbol `λ` which you can type in VS code using `\la `.

List has a specialized version of `map` defined as follows:
-/
def map (f : α → β) : List α → List β
  | []    => []
  | a::as => f a :: map f as

/-!
This is a very generic `map` function that can take any function that converts `(α → β)` and use it
to convert `List α → List β`. Notice the function call `f a` above, this application of `f` is
producing the converted items for the new list.

Let's look at some more examples:

-/
-- List String → List Nat
#eval ["elephant", "tiger", "giraffe"].map (fun s => s.length)
-- [8, 5, 7]

-- List Nat → List Float
#eval [1,2,3,4,5].map (fun s => (s.toFloat) ^ 3.0)
-- [1.000000, 8.000000, 27.000000, 64.000000, 125.000000]

--- List String → List String
#eval ["chris", "david", "mark"].map (fun s => s.capitalize)
-- ["Chris", "David", "Mark"]
/-!

Another example of a functor is the `Option` type. Option contains a value or nothing and is handy
for code that has to deal with optional values, like optional command line arguments.

Remember you can construct an Option using the type constructors `some` or `none`:

-/
#check some 5 -- Option Nat
#eval some 5  -- some 5
#eval (some 5).map (fun x => x + 1) -- some 6
#eval (some 5).map (fun x => toString x) -- some "5"
/-!

Lean also provides a convenient short hand syntax for `(fun x => x + 1)`, namely `(· + 1)`
using the middle dot unicode character which you can type in VS code using `\. `.

-/
#eval (some 4).map (· * 5)  -- some 20
/-!

The `map` function preserves the `none` state of the Option, so again
map preserves the structure of the object.

-/
def x : Option Nat := none
#eval x.map (fun x => toString x) -- none
#check x.map (fun x => toString x) -- Option String
/-!

Notice that even in the `none` case it has transformed `Option Nat` into `Option String` as
you see in the `#check` command.

## How to make a Functor Instance?

The `List` type is made an official `Functor` by the following type class instance:

-/
instance : Functor List where
  map := List.map
/-!

Notice all you need to do is provide the `map` function implementation.  For a quick
example, let's supposed you create a new type describing the measurements of a home
or apartment:

-/
structure LivingSpace (α : Type) where
  totalSize : α
  numBedrooms : Nat
  masterBedroomSize : α
  livingRoomSize : α
  kitchenSize : α
  deriving Repr, BEq
/-!

Now you can construct a `LivingSpace` in square feet using floating point values:
-/
abbrev SquareFeet := Float

def mySpace : LivingSpace SquareFeet :=
  { totalSize := 1800, numBedrooms := 4, masterBedroomSize := 500,
    livingRoomSize := 900, kitchenSize := 400 }
/-!

Now, suppose you want anyone to be able to map a `LivingSpace` from one type of measurement unit to
another.  Then you would provide a `Functor` instance as follows:

-/
def LivingSpace.map (f : α → β) (s : LivingSpace α) : LivingSpace β :=
  { totalSize := f s.totalSize
    numBedrooms := s.numBedrooms
    masterBedroomSize := f s.masterBedroomSize
    livingRoomSize := f s.livingRoomSize
    kitchenSize := f s.kitchenSize }

instance : Functor LivingSpace where
  map := LivingSpace.map
/-!

Notice this functor instance takes `LivingSpace` and not the fully qualified type `LivingSpace SquareFeet`.
Notice below that `LivingSpace` is a function from Type to Type.  For example, if you give it type `SquareFeet`
it gives you back the fully qualified type `LivingSpace SquareFeet`.

-/
#check LivingSpace -- Type → Type
/-!

So the `instance : Functor` then is operating on the more abstract, or generic `LivingSpace` saying
for the whole family of types `LivingSpace α` you can map to `LivingSpace β` using the generic
`LivingSpace.map` map function by simply providing a function that does the more primitive mapping
from `(f : α → β)`.  So `LivingSpace.map` is a sort of function applicator.
This is called a "higher order function" because it takes a function as input
`(α → β)` and returns another function as output `F α → F β`.

Notice that `LivingSpace.map` applies a function `f` to convert the units of all the LivingSpace
fields, except for `numBedrooms` which is a count (and therefore is not a measurement that needs
converting).

So now you can define a simple conversion function, let's say you want square meters instead:

-/
abbrev SquareMeters := Float
def squareFeetToMeters (ft : SquareFeet ) : SquareMeters := (ft / 10.7639104)
/-!

and now bringing it all together you can use the simple function `squareFeetToMeters` to map
`mySpace` to square meters:

-/
#eval mySpace.map squareFeetToMeters
/-
{ totalSize := 167.225472,
  numBedrooms := 4,
  masterBedroomSize := 46.451520,
  livingRoomSize := 83.612736,
  kitchenSize := 37.161216 }
  -/
/-!

Lean also defines custom infix operator `<$>` for `Functor.map` which allows you to write this:
-/
#eval (fun s => s.length) <$> ["elephant", "tiger", "giraffe"] -- [8, 5, 7]
#eval (fun x => x + 1) <$> (some 5) -- some 6
/-!

Note that the infix operator is left associative which means it binds more tightly to the
function on the left than to the expression on the right, this means you can often drop the
parentheses on the right like this:

-/
#eval (fun x => x + 1) <$> some 5 -- some 6
/-!

Note that Lean lets you define your own syntax, so `<$>` is nothing special.
You can define your own infix operator like this:

-/
infixr:100 " doodle " => Functor.map

#eval (· * 5) doodle [1, 2, 3]  -- [5, 10, 15]

/-!
Wow, this is pretty powerful.  By providing a functor instance on `LivingSpace` with an
implementation of the `map` function it is now super easy for anyone to come along and
transform the units of a `LivingSpace` using very simple functions like `squareFeetToMeters`. Notice
that squareFeetToMeters knows nothing about `LivingSpace`.

## How do Functors help with Monads ?

Functors are an abstract mathematical structure that is represented in Lean with a type class. The
Lean functor defines both `map` and a special case for working on constants more efficiently called
`mapConst`:

```lean
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α
```

Note that `mapConst` has a default implementation, namely:
`mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)` in the `Functor`
type class.  So you can use this default implementation and you only need to replace it if
your functor has a more specialized variant than this (usually the custom version is more performant).

In general then, a functor is a function on types `F : Type u → Type v` equipped with an operator
called `map` such that if you have a function `f` of type `α → β` then `map f` will convert your
container type from `F α → F β`. This corresponds to the category-theory notion of
[functor](https://en.wikipedia.org/wiki/Functor) in the special case where the category is the
category of types and functions between them.

Understanding abstract mathematical structures is a little tricky for most people. So it helps to
start with a simpler idea like functors before you try to understand monads.  Building on
functors is the next abstraction called [Applicatives](applicatives.lean.md).
-/