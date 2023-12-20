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
  add x y := Array.zipWith x y (· + ·)

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

#eval #[1, 2] + #[3, 4]
-- #[4, 6]
```
Note that `x + y` is notation for `Add.add x y` in Lean.

The example above demonstrates how type classes are used to overload notation.
Now, we explore another application. We often need an arbitrary element of a given type.
Recall that types may not have any elements in Lean.
It often happens that we would like a definition to return an arbitrary element in a "corner case."
For example, we may like the expression ``head xs`` to be of type ``a`` when ``xs`` is of type ``List a``.
Similarly, many theorems hold under the additional assumption that a type is not empty.
For example, if ``a`` is a type, ``exists x : a, x = x`` is true only if ``a`` is not empty.
The standard library defines a type class ``Inhabited`` to enable type class inference to infer a
"default" or "arbitrary" element of an inhabited type.
Let us start with the first step of the program above, declaring an appropriate class:

```lean
# namespace Ex
class Inhabited (a : Sort u) where
  default : a

#check @Inhabited.default
-- Inhabited.default : {a : Sort u} → [self : Inhabited a] → a
# end Ex
```
Note `Inhabited.default` doesn't have any explicit argument.

An element of the class ``Inhabited a`` is simply an expression of the form ``Inhabited.mk x``, for some element ``x : a``.
The projection ``Inhabited.default`` will allow us to "extract" such an element of ``a`` from an element of ``Inhabited a``.
Now we populate the class with some instances:

```lean
# namespace Ex
# class Inhabited (a : Sort _) where
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
# class Inhabited (a : Sort _) where
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

## Chaining Instances

If that were the extent of type class inference, it would not be all that impressive;
it would be simply a mechanism of storing a list of instances for the elaborator to find in a lookup table.
What makes type class inference powerful is that one can *chain* instances. That is,
an instance declaration can in turn depend on an implicit instance of a type class.
This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.

For example, the following definition shows that if two types ``a`` and ``b`` are inhabited, then so is their product:
```lean
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)
```
With this added to the earlier instance declarations, type class instance can infer, for example, a default element of ``Nat × Bool``:
```lean
# namespace Ex
# class Inhabited (a : Sort u) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# opaque default [Inhabited a] : a :=
#  Inhabited.default
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)
-- (0, true)
# end Ex
```
Similarly, we can inhabit type function with suitable constant functions:
```lean
# namespace Ex
# class Inhabited (a : Sort u) where
#  default : a
# opaque default [Inhabited a] : a :=
#  Inhabited.default
instance [Inhabited b] : Inhabited (a -> b) where
  default := fun _ => default
# end Ex
```
As an exercise, try defining default instances for other types, such as `List` and `Sum` types.

The Lean standard library contains the definition `inferInstance`. It has type `{α : Sort u} → [i : α] → α`,
and is useful for triggering the type class resolution procedure when the expected type is an instance.
```lean
#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) :=
  rfl
```
You can use the command `#print` to inspect how simple `inferInstance` is.
```lean
#print inferInstance
```

## ToString

The polymorphic method `toString` has type `{α : Type u} → [ToString α] → α → String`. You implement the instance
for your own types and use chaining to convert complex values into strings. Lean comes with `ToString` instances
for most builtin types.
```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")
```
## Numerals

Numerals are polymorphic in Lean. You can use a numeral (e.g., `2`) to denote an element of any type that implements
the type class `OfNat`.
```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check (2 : Rational) -- Rational
#check (2 : Nat)      -- Nat
```
Lean elaborate the terms `(2 : Nat)` and `(2 : Rational)` as
`OfNat.ofNat Nat 2 (instOfNatNat 2)` and
`OfNat.ofNat Rational 2 (instOfNatRational 2)` respectively.
We say the numerals `2` occurring in the elaborated terms are *raw* natural numbers.
You can input the raw natural number `2` using the macro `nat_lit 2`.
```lean
#check nat_lit 2  -- Nat
```
Raw natural numbers are *not* polymorphic.

The `OfNat` instance is parametric on the numeral. So, you can define instances for particular numerals.
The second argument is often a variable as in the example above, or a *raw* natural number.
```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

Because many users were forgetting the `nat_lit` when defining `OfNat` instances, Lean also accepts `OfNat` instance
declarations not using `nat_lit`. Thus, the following is also accepted.
```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α 1 where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

## Output parameters

By default, Lean only tries to synthesize an instance `Inhabited T` when the term `T` is known and does not
contain missing parts. The following command produces the error
"failed to create type class instance for `Inhabited (Nat × ?m.1499)`" because the type has a missing part (i.e., the `_`).
```lean
# -- FIXME: should fail
#check (inferInstance : Inhabited (Nat × _))
```
You can view the parameter of the type class `Inhabited` as an *input* value for the type class synthesizer.
When a type class has multiple parameters, you can mark some of them as output parameters.
Lean will start type class synthesizer even when these parameters have missing parts.
In the following example, we use output parameters to define a *heterogeneous* polymorphic
multiplication.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12
#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
# end Ex
```
The parameters `α` and `β` are considered input parameters and `γ` an output one.
Given an application `hMul a b`, after types of `a` and `b` are known, the type class
synthesizer is invoked, and the resulting type is obtained from the output parameter `γ`.
In the example above, we defined two instances. The first one is the homogeneous
multiplication for natural numbers. The second is the scalar multiplication for arrays.
Note that, you chain instances and generalize the second instance.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12
#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]
#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]
#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]
# end Ex
```
You can use our new scalar array multiplication instance on arrays of type `Array β`
with a scalar of type `α` whenever you have an instance `HMul α β γ`.
In the last `#eval`, note that the instance was used twice on an array of arrays.

## Default instances

In the class `HMul`, the parameters `α` and `β` are treated as input values.
Thus, type class synthesis only starts after these two types are known. This may often
be too restrictive.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

# -- TODO: fix error message
-- Error "failed to create type class instance for HMul Int ?m.1767 (?m.1797 x)"
-- #check fun y => xs.map (fun x => hMul x y)
# end Ex
```
The instance `HMul` is not synthesized by Lean because the type of `y` has not been provided.
However, it is natural to assume that the type of `y` and `x` should be the same in
this kind of situation. We can achieve exactly that using *default instances*.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)  -- Int -> List Int
# end Ex
```
By tagging the instance above with the attribute `default_instance`, we are instructing Lean
to use this instance on pending type class synthesis problems.
The actual Lean implementation defines homogeneous and heterogeneous classes for arithmetical operators.
Moreover, `a+b`, `a*b`, `a-b`, `a/b`, and `a%b` are notations for the heterogeneous versions.
The instance `OfNat Nat n` is the default instance (with priority `100`) for the `OfNat` class. This is why the numeral
`2` has type `Nat` when the expected type is not known. You can define default instances with higher
priority to override the builtin ones.
```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[default_instance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- Rational
```
Priorities are also useful to control the interaction between different default instances.
For example, suppose `xs` has type `α`, when elaboration `xs.map (fun x => 2 * x)`, we want the homogeneous instance for multiplication
to have higher priority than the default instance for `OfNat`. This is particularly important when we have implemented only the instance
`HMul α α α`, and did not implement `HMul Nat α α`.
Now, we reveal how the notation `a*b` is defined in Lean.
```lean
# namespace Ex
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * "  => HMul.hMul
# end Ex
```
The `Mul` class is convenient for types that only implement the homogeneous multiplication.

## Scoped Instances

TODO

## Local Instances

TODO
