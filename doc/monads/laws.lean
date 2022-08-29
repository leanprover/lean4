/-!
# Monad Laws

In the previous sections you learned how to use [Functors](functors.lean.md),
[Applicatives](applicatives.lean.md), and [Monads](monads.lean.md), and you played with some useful
instances including [Option](monads.lean.md), [IO](monads.lean.md), [Reader](readers.lean.md),
[State](states.lean.md) and [Except](except.lean.md) and you learned about composition using [Monad
Transformers](transformers.lean.md).

So far, you've learned the concrete details you need in order to _use_ monads in your Lean programs.
But there's still one more important concept you need if you want to _create_ new functors,
applicatives and monads. Namely, the notion of _structural “laws”_ -- rules that these type
classes should follow in order to meet other programmers' expectations about your code.

# Life without Laws

Remember Lean represents each of our abstract classes by a type class. Each of these type classes
has one or two main functions. So, as long as we implement those functions and it type checks, we
have a new functor, applicative, or monad, right?

Well not quite. Yes, your program will compile and you'll be able to use the instances. But this
doesn't mean your instances follow the mathematical constructs. If they don't, your instances won't
fulfill other programmers' expectations. Each type class has its own “laws”. For instance, suppose
you have the following Point Functor:
-/
structure Point (α: Type) where
  x : α
  y : α
  deriving Repr, BEq

def Point.map (f : α → β) (s : Point α) : Point β :=
  { x := f s.y,  -- an example of something weird
    y := f s.x }

instance : Functor Point where
  map := Point.map

#eval (.+2) <$> (Point.mk 1 2) -- { x := 4, y := 3 }

/-!
This Point does something weird, when you `map` it because it transposes the `x` and `y` coordinates
which is not what other people would expect from a map function.  In fact, it breaks the rules
as you will see below.

## What are the Functor laws?

Functors have two laws: the _identity_ law, and the _composition_ law. These laws express behaviors that
your functor instances should follow. If they don't, other programmers will be very confused at the
effect your instances have on the program. Many structures have similar laws, including monads.

The identity law says that if you "map" the identity function (`id`) over your functor, the
resulting functor should be the same. A succinct way of showing this on a `List` functor is:

-/
def list1 := [1,2,3]

#eval id <$> list1 == list1 -- true
/-!

Now let's try the same test on our `Point` functor:
-/

def p1 : Point Nat := (Point.mk 1 2)

#eval id <$> p1 == p1 -- false

/-!
Oh, and look while the List is behaving well, our `Point` functor fails this identity test.

The _composition_ law says that if we "map" two functions in succession over our functor, this
should be the same as "composing" the functions and simply mapping that one super-function over our
functor.  In Lean you can compose two functions using `Function.comp f g` (or the syntax `f ∘ g`,
which you can type in VS code using `\o `) and you will get the same results from both of these
showing that the composition law holds for `List Nat`:

-/
def double (x: Nat) := x + x
def square (x: Nat) := x * x

#eval (double <$> (square <$> list1)) -- [2, 8, 18]

#eval (double <$> (square <$> list1)) == ((double ∘ square) <$> list1) -- true

-- ok, what about our Point class?
#eval double <$> (square <$> p1) -- { x := 2, y := 8 }
#eval (double ∘ square) <$> p1   -- { x := 8, y := 2 }

#eval double <$> (square <$> p1) == (double ∘ square) <$> p1  -- false
/-!
Note that composition also fails on our bad `Point` because the x/y transpose.

As you can see this bad `Point` implementation violates both of the functor laws. In this case it
would not be a true functor. Its behavior would confuse any other programmers trying to use it. You
should take care to make sure that your instances make sense. Once you get a feel for these type
classes, the likelihood is that the instances you'll create follow the laws.

Hopefully this explains the value of these laws.  We won't show any more bad implementations!

## What are the Applicative Laws?

While functors have two laws, applicatives have four laws which we can test using our applicative
list:

- Identity
- Homomorphism
- Interchange
- Composition

### Identity

`pure id <*> v = v`

Applying the identity function through an applicative structure should not change the underlying
values or structure.  For example:
-/
instance : Applicative List where
  pure := List.pure
  seq f x := List.bind f fun y => Functor.map y (x ())

#eval pure id <*> [1, 2, 3]  -- [1, 2, 3]
/-!

The `pure id` statement here is wrapping the identity function in our applicative structure
so that we can apply that over our container `[1, 2, 3]` using the Applicative `seq` operation
which has the notation `<*>`.

We can prove this for all values `v` and any applicative `m` with this theorem:
-/
example [Applicative m] [LawfulApplicative m] (v : m α) :
  pure id <*> v = v :=
  by simp -- Goals accomplished 🎉
/-!

### Homomorphism

`pure f <*> pure x = pure (f x)`

Suppose you wrap a function and an object in pure. You can then apply the wrapped function over the
wrapped object. Of course, we could also apply the normal function over the normal object, and then
wrap it in pure. The homomorphism law states these results should be the same.

For example:

-/
def x := 1
def f := (· + 2)

#eval pure f <*> pure x = (pure (f x) : List Nat) -- true
/-!

You should see a distinct pattern here. The overriding theme of almost all these laws is that our
type classes are containers. The type class function should not have any side effects. All they
should do is facilitate the wrapping, unwrapping, and transformation of data contained in the
container resulting in a new container that has the same structure.

### Interchange

`u <*> pure y = pure (. y) <*> u`.

This law is is a little more complicated, so don't sweat it too much. It states that the order that
we wrap things shouldn't matter. One the left, we apply any applicative over a pure wrapped object.
On the right, we first wrap a function applying the object as an argument. Note that `(· y)` is short
hand for: `fun f => f y`. Then we apply this to the first applicative. These should be the same.

For example:

-/
def y := 4
def g : List (Nat → Nat) := [(· + 2)]

#eval g <*> pure y = pure (· y) <*> g      -- true
/-!

You can prove this with the following theorem:
-/
example [Applicative m] [LawfulApplicative m] (u : m (α → β)) (y : α) :
  u <*> pure y = pure (· y) <*> u :=
  by simp [pure_seq] -- Goals accomplished 🎉

/-!

### Composition:

`u <*> v <*> w = u <*> (v <*> w)`

This final applicative law mimics the second functor law. It is a composition law. It states that
function composition holds across applications within the applicative:

For example:

-/
def u := [1, 2]
def v := [3, 4]
def w := [5, 6]

#eval pure (·+·+·) <*> u <*> v <*> w
-- [9, 10, 10, 11, 10, 11, 11, 12]

#eval let grouping := pure (·+·) <*> v <*> w
      pure (·+·) <*> u <*> grouping
-- [9, 10, 10, 11, 10, 11, 11, 12]
/-!

With composition we implemented the grouping `(v <*> w)` then showed you could
use that in the outer sequence `u <*> grouping` to get the same final result `[9, 10, 10, 11, 10, 11, 11, 12]`.

## What are the Monad Laws?

Monads have three laws:

- Left Identity
- Right Identity
- Associativity

### Left Identity

Identity laws for monads specify that `pure` by itself shouldn't really change anything
about the structure or its values.

Left identity is `x >>= pure = x` and is demonstrated by the following examples on a
monadic `List`:
-/
instance : Monad List  where
  pure := List.pure
  bind := List.bind

#eval ["apple", "orange"] >>= pure  -- ["apple", "orange"]
#eval [1,2,3] >>= pure              -- [1,2,3]
/-!

### Right Identity

Right identity is `pure x >>= f = f x` and is demonstrated by the following example:
-/
def h (x: Nat) : Option Nat :=  some (x + 1)
def z := 5

#eval pure z >>= h                  -- some 6
#eval h z                           -- some 6

-- so in this example with this specific `z` and `h` we see that the rule holds true:
#eval pure z >>= h = h x            -- true
/-!

### Associativity

The associativity law is written as:
```lean,ignore
  x >>= f >>= g = x >>= (λ x => f x >>= g)
```
where `(x : m α)` and `(f : α → m β)` and `(g : β → m γ)`.

The associativity law is difficult to parse like some of the applicative laws, but what it is saying
is that if you change the grouping of `bind` operations, you should still get the same result.
This law has a parallel structure to the other composition laws.

You can see this in action in the following rewrite of `runOptionFuncsBind` from [monads](monads.lean.md):
-/
def optionFunc1 : String -> Option Nat
| "" => none
| str => some str.length

def optionFunc2 (i : Nat) : Option Float :=
  if i % 2 == 0 then none else some (i.toFloat * 3.14159)

def optionFunc3 (f : Float) : Option (List Nat) :=
  if f > 15.0 then none else some [f.floor.toUInt32.toNat, f.ceil.toUInt32.toNat]


def runOptionFuncsBind (input: String) : Option (List Nat) :=
   optionFunc1 input >>= optionFunc2 >>= optionFunc3

def runOptionFuncsBindGrouped (input: String) : Option (List Nat) :=
   optionFunc1 input >>= (λ x => optionFunc2 x >>= optionFunc3)

#eval runOptionFuncsBind "big"        -- some [9, 10]
#eval runOptionFuncsBindGrouped "big" -- some [9, 10]
/-!

Notice here we had to insert a `λ` function just like the definition says: `(λ x => f x >>= g)`.
This is because unlike applicatives, we can't resolve the structure of later operations without the
results of earlier operations quite as well because of the extra context monads provide. But we can
still group their later operations into composite functions taking their inputs from earlier on, and
the result should be the same.


## Summary

While these laws may be a bit difficult to understand just by looking at them, the good news is that
most of the instances you'll make will naturally follow the laws so long as you keep it simple, so
you shouldn't have to worry about them too much.

So in summary, there are two main ideas from all the laws:

1. Applying the identity or pure function should not change the underlying values or structure.
1. It should not matter what order we group operations in.  Another way to state this is function
   composition should hold across your structures.

Following these laws will ensure other programmers are not confused by the bahavior of your
new functors, applicatives and monads.

-/
