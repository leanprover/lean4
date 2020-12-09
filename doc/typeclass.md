# Type classes

Typeclasses were introduced as a principled way of enabling
ad-hoc polymorphism in functional programming languages. We first observe that it
would be easy to implement an ad-hoc polymorphic function (such as addition) if the
function simply took the type-specific implementation of addition as an argument
and then called that implementation on the remaining arguments. For example,
suppose we declare a structure in Lean to hold implementations of addition
```lean
# namespace Ex
structure Add (a : Type) where
  add : a -> a -> a

#check @Add.add
-- Add.add : {a : Type} → Add a → a → a → a
# end Ex
```
In the above Lean code, the field `add` has type
`Add.add : {α : Type} → Add α → α → α → α`
where the curly braces around the type `a` mean that it is an implicit argument.
We could implement `double` by
```lean
# namespace Ex
# structure Add (a : Type) where
#  add : a -> a -> a
def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10
-- 100

#eval double { add := Int.add } 10
-- 20

# end Ex
```
Note that you can double a natural number `n` by `double { add := Nat.add } n`.
Of course, it would be highly cumbersome for users to manually pass the
implementations around in this way.
Indeed, it would defeat most of the potential benefits of ad-hoc
polymorphism.

The main idea behind typeclasses is to make arguments such as `Add a` implicit,
and to use a database of user-defined instances to synthesize the desired instances
automatically through a process known as typeclass resolution. In Lean, by changing
`structure` to `class` in the example above, the type of `Add.add` becomes
```lean
# namespace Ex
class Add (a : Type) where
  add : a -> a -> a

#check @Add.add
-- Add.add : {a : Type} → [self : Add a] → a → a → a
# end Ex
```
where the square brackets indicate that the argument of type `Add a` is *instance implicit*,
i.e. that it should be synthesized using typeclass resolution. This version of
`add` is the Lean analogue of the Haskell term `add :: Add a => a -> a -> a`.
Similarly, we can register an instance by
```lean
# namespace Ex
# class Add (a : Type) where
#  add : a -> a -> a
instance : Add Nat where
  add := Nat.add

# end Ex
```
Then for `n : Nat` and `m : Nat`, the term `Add.add n m` triggers typeclass resolution with the goal
of `Add Nat`, and typeclass resolution will synthesize the instance above. In
general, instances may depend on other instances in complicated ways. For example,
you can declare an (anonymous) instance stating that if `a` has addition, then `Array a`
has addition:
```lean
instance [Add a] : Add (Array a) where
  add x y := Array.zipWith x y (. + .)

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

#eval #[1, 2] + #[3, 4]
-- #[4, 6]
```
Note that `x + y` is notation for `Add.add x y` in Lean.

The example above demonstrates how type classes are used to overload notation.
Now, we explore another application. We often need an arbitrary element of a given type.
Recall that types may not have any elements in Lean.
It often happens that we would like a definition to return an arbitraryt element in a "corner case."
For example, we may like the expression ``head xs`` to be of type ``a`` when ``xs`` is of type ``List a``.
Similarly, many theorems hold under the additional assumption that a type is not empty.
For example, if ``a`` is a type, ``exists x : a, x = x`` is true only if ``a`` is not empty.
The standard library defines a type class ``Inhabited`` to enable type class inference to infer a
"default" or "arbitrary" element of an inhabited type.
Let us start with the first step of the program above, declaring an appropriate class:

```lean
# namespace Ex
class Inhabited (a : Type u) where
  default : a

#check @Inhabited.default
-- Inhabited.default : {a : Type u} → [self : Inhabited a] → a
# end Ex
```
Note `Inhabited.default` doesn't have any explicit argument.

An element of the class ``Inhabited a`` is simply an expression of the form ``Inhabited.mk x``, for some element ``x : a``.
The projection ``Inhabited.default`` will allow us to "extract" such an element of ``a`` from an element of ``Inhabited a``.
Now we populate the class with some instances:

```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- 0

#eval (Inhabited.default : Bool)
-- true
# end Ex
```
You can use the command `export` to create the alias `default` for `Inhabited.default`
```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# instance : Inhabited Unit where
#  default := ()
# instance : Inhabited Prop where
#  default := True
export Inhabited (default)

#eval (default : Nat)
-- 0

#eval (default : Bool)
-- true
# end Ex
```
Sometimes we want to think of the default element of a type as being an *arbitrary* element, whose specific value should not play a role in our proofs.
For that purpose, we can write ``arbitrary`` instead of ``default``. We define ``arbitrary`` as an *opaque* constant.
Opaque constants are never unfolded by the type checker.
```lean
# namespace Ex
# export Inhabited (default)
theorem defNatEq0 : (default : Nat) = 0 :=
  rfl

constant arbitrary [Inhabited a] : a :=
  Inhabited.default

-- theorem arbitraryNatEq0 : (arbitrary : Nat) = 0 :=
--   rfl
/-
error: type mismatch
  rfl
has type
  arbitrary = arbitrary
but is expected to have type
  arbitrary = 0
-/
# end Ex
```
The theorem `defNatEq0` type checks because the type checker can unfold `(default : Nat)` and reduce it to `0`. This is not the case in the theorem `arbitraryNatEq0` because `arbitrary` is an opaque constant.

## Chaining Instances

If that were the extent of type class inference, it would not be all that impressive;
it would be simply a mechanism of storing a list of instances for the elaborator to find in a lookup table.
What makes type class inference powerful is that one can *chain* instances. That is,
an instance declaration can in turn depend on an implicit instance of a type class.
This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.

For example, the following definition shows that if two types ``a`` and ``b`` are inhabited, then so is their product:
```lean
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (arbitrary, arbitrary)
```
With this added to the earlier instance declarations, type class instance can infer, for example, a default element of ``Nat × Bool``:
```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# constant arbitrary [Inhabited a] : a :=
#  Inhabited.default
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (arbitrary, arbitrary)

#eval (arbitrary : Nat × Bool)
-- (0, true)
# end Ex
```
Similarly, we can inhabit tyhe function with suitable constant functions:
```lean
instance [Inhabited b] : Inhabited (a -> b) where
  default := fun _ => arbitrary
```
As an exercise, try defining default instances for other types, such as `List` and `Sum` types.

## Local instances

TODO

## Scoped Instances

TODO