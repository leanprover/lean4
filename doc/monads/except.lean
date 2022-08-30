/-!
# Except

The `Except` Monad adds exception handling behavior to your functions.  Exception handling
in other languages like Python or Java is done with a built in `throw` method that you
can use anywhere.  In `Lean` you can only `throw` an exception when your function is
executing in the context of an `Except` monad.

-/
def divide (x y: Float): Except String Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    pure (x / y)

#eval divide 5 2  -- Except.ok 2.500000
#eval divide 5 0  -- Except.error "can't divide by zero"

/-!

Just as the `read` operation was available from the `ReaderM` monad and the `get` and `set`
operations came with the `StateM` monad, here we see a `throw` operation is provided by the `Except`
monad.

So in Lean, `throw` is not available everywhere like it is in most imperative programming languages.
You have to declare your function can throw by changing the type signature to `Except String Float`.
This creates a function that might return an error of type `String` or it might return a value of
type `Float` in the non-error case.

Once your function is monadic you also need to use the `pure` constructor of the `Except` monad to
convert the pure non-monadic value `x / y` into the required `Except` object.  See
[Applicatives](applicatives.lean.md) for details on `pure`.

Now this return typing would get tedious if you had to include it everywhere that you call this
function, however, Lean type inference can clean this up. For example, you can define a test
function can calls the `divide` function and you don't need to say anything here about the fact that
it might throw an error, because that is inferred:
-/
def test := divide 5 0

#check test     -- Except String Float
/-!

Notice the Lean compiler infers the required `Except String Float` type information for you.
And now we can run this test and get the expected exception:

-/
#eval test      -- Except.error "can't divide by zero"
/-!

## Chaining

Now as before you can build a chain of monadic actions that can be composed together using `bind (>>=)`:
-/
def square (x : Float) : Except String Float :=
  if x >= 100 then
    throw "it's absolutely huge"
  else
    pure (x * x)

#eval divide 6 2 >>= square  -- Except.ok 9.000000
#eval divide 6 0 >>= square  -- Except.error "can't divide by zero"
#eval divide 100 1 >>= square  -- Except.error "it's absolutely huge"

def chainUsingDoNotation := do
  let r ← divide 6 0
  square r

#eval chainUsingDoNotation  -- Except.error "can't divide by zero"

/-!
Notice in the second `divide 6 0` the exception from that division was nicely propagated along
to our final result and the square function was pretty much ignored in that case.

Remember also that you can chain the actions with implicit binding by using the `do` notation
as you see in the `chainUsingDoNotation` function above.

## Try/Catch

Now with all good exception handling you also want to be able to catch exceptions so your program
can try continue on or do some error recovery task, which you can do like this:
-/
def testCatch :=
  try
    let r ← divide 8 0  -- 'r' is type Float
    pure (toString r)
  catch e =>
    pure s!"Caught exception: {e}"
/-!

Note that the type inferred by Lean for this function is `Except String String` so the `Except
String Float` return type from the divide has been transformed. The secret to Lean is how easily it
does monad transformation for you in most cases.  Notice here you didn't have to do any extra work
for the compiler to figure out the transform you were trying to do.

You can now see the try/catch working in this eval:
-/
#eval testCatch -- Except.ok "Caught exception: can't divide by zero"
/-!

Notice the `Caught exception:` wrapped message is returned, and that it is returned as an
`Except.ok` value, meaning `testCatch` eliminated the error result as expected.

So we've interleaved a new concept into our functions (exception handling) and the compiler is still
able to type check everything just as well as it does for pure functions and it's been able to infer
some things along the way to make it even easier to manage.

Now you might be wondering why `testCatch` doesn't have return type `String`? Lean does this as a
convenience since you could have a rethrow in or after the catch block. If you really want to stop
the `Except` type from bubbling up you can unwrap it like this:

-/
def testUnwrap : String := Id.run do
  let r ← divide 8 0 -- r is type Except String Float
  match r with
  | .ok a => toString a -- 'a' is type Float
  | .error e => s!"Caught exception: {e}"

#check testUnwrap -- String
#eval testUnwrap -- "Caught exception: can't divide by zero"

/-!

The `Id.run` function is a helper function that executes the `do` block and returns the result where
`Id` is the _identity monad_.  So `Id.run do` is a pattern you can use to execute monads in a
function that is not itself monadic.

## Summary

Now that you know all these different monad constructs, you might be wondering how you can combine
them. What if there was some part of your state that you wanted to be able to modify (using the
State monad), but you also needed exception handling. How can you get multiple monadic capabilities
in the same fuunction. To learn the answer, head to [Monad Transformers](transformers.lean.md).

-/