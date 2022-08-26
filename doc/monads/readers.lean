/-!
# Readers

In [part 3: Monads](monads.lean.md) you learned about the conceptual idea of monads. You learned
what they are, and saw how some common types like `IO` and `Option` work as monads. Now in this
part, we'll start looking at some other useful monads. In particular, we'll consider the `Reader`
monad.

## How to do Global Variables in Lean?

In Lean, your code is generally "pure", meaning functions can only interact with the arguments
passed to them. This effectively means you cannot have global variables. You can have global
definitions, but these are fixed at compile time. If some user behavior might change them, we have
to wrap them in the `IO` monad, which means they can't be used from pure code.

Consider this example. Here, we want to have an `Environment` containing different parameters as a
global variable. However, we want to load these parameters from the process environment variables,
which requires the `IO` monad.
-/

structure Environment where
  path : String
  home : String
  user : String
  deriving Repr

def getEnvDefault (name: String): IO String :=
  return match (← IO.getEnv name) with
  | none => ""
  | some s => s

def loadEnv : IO Environment := do
  let path ← getEnvDefault "PATH"
  let home ← getEnvDefault "HOME"
  let user ← getEnvDefault "USER"
  return { path, home, user }

def func1 (e : Environment) : Float :=
  let l1 := e.path.length
  let l2 := e.home.length * 2
  let l3 := e.user.length * 3
  (l1 + l2 + l3).toFloat * 2.1

def func2 (env: Environment) : Nat :=
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
ultimately pass it to func1. In a language with global variables, we could save env as a global
value in main. Then func1 could access it directly. There would be no need to have it as a parameter
to func1, func2 and func3. In larger programs, these "pass-through" variables can cause a lot of
headaches.

## The Reader Solution

The Reader monad solves this problem. It effectively creates a global read-only value of a specified
type. All functions within the monad can "read" the type. Let's look at how the Reader monad changes
the shape of our code. Our functions **no longer need** the `Environment` as an explicit parameter, as
they can access it through the monad.
-/

def readerFunc1 : Reader Environment Float := do
  let env ← read
  let l1 := env.path.length
  let l2 := env.home.length * 2
  let l3 := env.user.length * 3
  return (l1 + l2 + l3).toFloat * 2.1

def readerFunc2 : Reader Environment Nat :=
  readerFunc1 >>= (fun x => return 2 + (x.floor.toUInt32.toNat))

def readerFunc3 : Reader Environment String := do
  let x ← readerFunc2
  return "Result: " ++ (toString x)

def main2 : IO Unit := do
  let env ← loadEnv
  let str := readerFunc3 env
  IO.println str

#eval main2 -- Result: 7538
/-!
`main2` loads the environment as before, and estabilishes the `Reader` state by passing `env` to
readerFunc3.  The `do` notation you learned about in [Monads](monads.lean.md) is hiding some things
here.  Technically `readerFunc3` is a monadic action and in order to "run" that action the `Reader`
monad provides a `run` method and it is the `Reader` run method that takes the initial `Environment`
state.  So you can actually write the complete code by doing this: `let str := readerFunc3.run env`.
eliminiates eliminiates
**Side note**: If the function `readerFunc3` also took some explicit arguments then you would have
to write `(readerFunc3 args).run env` and this is a bit ugly, so Lean provides an infix operator
`|>` that eliminiates those parens so you can write `readerFunc3 args |>.run env` and then you can
chain multiple monadic actions like this `m1 args1 |>.run args2 |>.run args3` and this is the
recommended style.  You will see this patten used heavily in Lean code.

The `let env ← read` expression in `readerFunc1` unwraps the environment from the `Reader` so we can
use it. Each type of monad might provide one or more extra functions like this, functions that
become available only when you are in the context of that monad.

Here the `readerFunc2` function uses the `bind` operator `>>=` just to show you that there are bind
operations happening here.  The `readerFunc3` function uses the  `do` notation you learned about in
[Monads](monads.lean.md) which hides that bind operation and can make the code look cleaner.

The `do` notation with `let x ← readerFunc2` is also calling the `run` function to actually execute
the monadic action, then it unwraps the value x, so it is really doing `let x ← readerFunc2.run`.

The important difference here to the earlier code is that `readerFunc3` and `readerFunc2` no longer
have an **explicit** Environment input parameter that needs to be passed along all the way to
`readerFunc1`.  Instead, the `Reader` monad is taking care of that for you, which gives you the
illusion of something like global state where the state is now available to all functions that use
the `Reader` monad.

The above code also introduces an important idea. Whenever you learn about a monad "X", there's
often (but not always) a `run` function to execute that monad, and sometimes some additional
functions like `read` that interact with the monad state.

You might be wondering, how does the state actually move through the Reader monad? How can
you add an input argument to a function by modifying it's return type?  There is a special
command in the Lean interpreter that will show you the reduced Types:
-/
#reduce Reader Environment String   -- Environment → String
/-!
And you can see here that this type is actually a function!  It's a function that takes an
`Environment` as input and returns a `String`.  So, remember in Lean that a function that takes
argument a and returns a string: `def f (a: Nat) → String` is the same as the function that takes no
arguments and returns another function of type `Nat → String`.  Well this fact is being used by the
Reader Monad to add an input argument to all the functions that use the Reader monad and this is why
`main` is able to start things off by simply passing that new input argument in `readerFunc3 env`.
So now that you know the implementation details of the Reader monad you can see that what it is
doing looks very much like the original code we wrote at the beginning of this section, only it's
taking a lot of the tedious work off your plate and it is creating a nice clean separation between
what your pure functions are doing, and the global state idea that the Reader adds.

## Conclusion

It might not seem like we've accomplished much with this `Reader Environment` monad, but you will
find that in larger code bases, with many different types of monads all composed together this
greatly cleans up the code. Monads provide a beautiful functional way of managing cross-cutting
concerns that would otherwise make your code very messy.

Now it's time to move on to [part 5: State Monad](states.lean.md) which is like a `Reader` that is
also updatable.
-/

