/-!
# Readers

In the [previous section](monads.lean.md) you learned about the conceptual idea of monads. You learned
what they are, and saw how some common types like `IO` and `Option` work as monads. Now in this
section, you will be looking at some other useful monads. In particular, the `ReaderM` monad.

## How to do Global Variables in Lean?

In Lean, your code is generally "pure", meaning functions can only interact with the arguments
passed to them. This effectively means you cannot have global variables. You can have global
definitions, but these are fixed at compile time. If some user behavior might change them, you would have
to wrap them in the `IO` monad, which means they can't be used from pure code.

Consider this example. Here, you want to have an `Environment` containing different parameters as a
global variable. However, you want to load these parameters from the process environment variables,
which requires the `IO` monad.
-/

structure Environment where
  path : String
  home : String
  user : String
  deriving Repr

def getEnvDefault (name : String): IO String := do
  let val? ← IO.getEnv name
  pure <| match val? with
          | none => ""
          | some s => s

def loadEnv : IO Environment := do
  let path ← getEnvDefault "PATH"
  let home ← getEnvDefault "HOME"
  let user ← getEnvDefault "USER"
  pure { path, home, user }

def func1 (e : Environment) : Float :=
  let l1 := e.path.length
  let l2 := e.home.length * 2
  let l3 := e.user.length * 3
  (l1 + l2 + l3).toFloat * 2.1

def func2 (env : Environment) : Nat :=
  2 + (func1 env).floor.toUInt32.toNat

def func3 (env : Environment) : String :=
  "Result: " ++ (toString (func2 env))

def main : IO Unit := do
  let env ← loadEnv
  let str := func3 env
  IO.println str

#eval main -- Result: 7538

/-!
The only function actually using the environment is func1. However func1 is a pure function. This
means it cannot directly call loadEnv, an impure function in the IO monad. This means the
environment has to be passed through as a variable to the other functions, just so they can
ultimately pass it to func1. In a language with global variables, you could save env as a global
value in main. Then func1 could access it directly. There would be no need to have it as a parameter
to func1, func2 and func3. In larger programs, these "pass-through" variables can cause a lot of
headaches.

## The Reader Solution

The `ReaderM` monad solves this problem. It effectively creates a global read-only value of a
specified type. All functions within the monad can "read" the type. Let's look at how the `ReaderM`
monad changes the shape of this code. Now the functions **no longer need** to be given the
`Environment` as an explicit parameter, as they can access it through the monad.
-/

def readerFunc1 : ReaderM Environment Float := do
  let env ← read
  let l1 := env.path.length
  let l2 := env.home.length * 2
  let l3 := env.user.length * 3
  return (l1 + l2 + l3).toFloat * 2.1

def readerFunc2 : ReaderM Environment Nat :=
  readerFunc1 >>= (fun x => return 2 + (x.floor.toUInt32.toNat))

def readerFunc3 : ReaderM Environment String := do
  let x ← readerFunc2
  return "Result: " ++ toString x

def main2 : IO Unit := do
  let env ← loadEnv
  let str := readerFunc3.run env
  IO.println str

#eval main2 -- Result: 7538
/-!
The `ReaderM` monad provides a `run` method and it is the `ReaderM` run method that takes the initial
`Environment` context.  So here you see `main2` loads the environment as before, and establishes
the `ReaderM` context by passing `env` to the `run` method.

> **Side note 1**: The `return` statement used above also needs some explanation.  The `return`
statement in Lean is closely related to `pure`, but a little different. First the similarity is that
`return` and `pure` both lift a pure value up to the Monad type. But `return` is a keyword so you do
not need to parenthesize the expression like you do when using `pure`.  (Note: you can avoid
parentheses when using `pure` by using the `<|` operator like we did above in the initial
`getEnvDefault` function).  Furthermore, `return` can also cause an early `return` in a monadic
function similar to how it can in an imperative language while `pure` cannot.

> So technically if `return` is the last statement in a function it could be replaced with `pure <|`,
but one could argue that `return` is still a little easier for most folks to read, just so long as
you understand that `return` is doing more than other languages, it is also wrapping pure values in
the monadic container type.

> **Side note 2**: If the function `readerFunc3` also took some explicit arguments then you would have
to write `(readerFunc3 args).run env` and this is a bit ugly, so Lean provides an infix operator
`|>` that eliminates those parentheses so you can write `readerFunc3 args |>.run env` and then you can
chain multiple monadic actions like this `m1 args1 |>.run args2 |>.run args3` and this is the
recommended style.  You will see this pattern used heavily in Lean code.

The `let env ← read` expression in `readerFunc1` unwraps the environment from the `ReaderM` so we
can use it. Each type of monad might provide one or more extra functions like this, functions that
become available only when you are in the context of that monad.

Here the `readerFunc2` function uses the `bind` operator `>>=` just to show you that there are bind
operations happening here.  The `readerFunc3` function uses the `do` notation you learned about in
[Monads](monads.lean.md) which hides that bind operation and can make the code look cleaner.
So the expression `let x ← readerFunc2` is also calling the `bind` function under the covers,
so that you can access the unwrapped value `x` needed for the `toString x` conversion.

The important difference here to the earlier code is that `readerFunc3` and `readerFunc2` no longer
have an **explicit** Environment input parameter that needs to be passed along all the way to
`readerFunc1`.  Instead, the `ReaderM` monad is taking care of that for you, which gives you the
illusion of something like global context where the context is now available to all functions that use
the `ReaderM` monad.

The above code also introduces an important idea. Whenever you learn about a monad "X", there's
often (but not always) a `run` function to execute that monad, and sometimes some additional
functions like `read` that interact with the monad context.

You might be wondering, how does the context actually move through the `ReaderM` monad? How can you
add an input argument to a function by modifying its return type?  There is a special command in
Lean that will show you the reduced types:
-/
#reduce ReaderM Environment String   -- Environment → String
/-!
And you can see here that this type is actually a function!  It's a function that takes an
`Environment` as input and returns a `String`.

Now, remember in Lean that a function that takes an argument of type `Nat` and returns a `String`
like `def f (a : Nat) : String` is the same as this function `def f : Nat → String`.  These are
exactly equal as types.  Well this is being used by the `ReaderM` Monad to add an input argument to
all the functions that use the `ReaderM` monad and this is why `main` is able to start things off by
simply passing that new input argument in `readerFunc3.run env`. So now that you know the implementation
details of the `ReaderM` monad you can see that what it is doing looks very much like the original
code we wrote at the beginning of this section, only it's taking a lot of the tedious work off your
plate and it is creating a nice clean separation between what your pure functions are doing, and the
global context idea that the `ReaderM` adds.

## withReader

One `ReaderM` function can call another with a modified version of the `ReaderM` context. You can
use the `withReader` function from the `MonadWithReader` type class to do this:

-/
def readerFunc3WithReader : ReaderM Environment String := do
  let x ← withReader (λ env => { env with user := "new user" }) readerFunc2
  return "Result: " ++ toString x

/-!
Here we changed the `user` in the `Environment` context to "new user" and then we passed that
modified context to `readerFunc2`.

So `withReader f m` executes monad `m` in the `ReaderM` context modified by `f`.

## Handy shortcut with (← e)

If you use the operator `←` in a let expression and the variable is only used once you can
eliminate the let expression and place the `←` operator in parentheses like this
call to loadEnv:
-/
def main3 : IO Unit := do
  let str := readerFunc3 (← loadEnv)
  IO.println str
/-!

## Conclusion

It might not seem like much has been accomplished with this `ReaderM Environment` monad, but you will
find that in larger code bases, with many different types of monads all composed together this
greatly cleans up the code. Monads provide a beautiful functional way of managing cross-cutting
concerns that would otherwise make your code very messy.

Having this control over the inherited `ReaderM` context via `withReader` is actually very useful
and something that is quite messy if you try and do this sort of thing with global variables, saving
the old value, setting the new one, calling the function, then restoring the old value, making sure
you do that in a try/finally block and so on. The `ReaderM` design pattern avoids that mess
entirely.

Now it's time to move on to [StateM Monad](states.lean.md) which is like a `ReaderM` that is
also updatable.
-/