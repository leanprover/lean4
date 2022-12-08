/-!
# Monad Transformers

In the previous sections you learned about some handy monads [Option](monads.lean.md),
[IO](monads.lean.md), [Reader](readers.lean.md), [State](states.lean.md) and
[Except](except.lean.md), and you now know how to make your function use one of these, but what you
do not yet know is how to make your function use multiple monads at once.

For example, suppose you need a function that wants to access some Reader context and optionally throw
an exception?  This would require composition of two monads `ReaderM` and `Except` and this is what
monad transformers are for.

A monad transformer is fundamentally a wrapper type. It is generally parameterized by another
monadic type. You can then run actions from the inner monad, while adding your own customized
behavior for combining actions in this new monad. The common transformers add `T` to the end of an
existing monad name. You will find `OptionT`, `ExceptT`, `ReaderT`, `StateT` but there is no transformer
for `IO`.  So generally if you need `IO` it becomes the innermost wrapped monad.

In the following example we use `ReaderT` to provide some read only context to a function
and this `ReaderT` transformer will wrap an `Except` monad.  If all goes well the
`requiredArgument` returns the value of a required argument and `optionalSwitch`
returns true if the optional argument is present.

-/
abbrev Arguments := List String

def indexOf? [BEq α] (xs : List α) (s : α) (start := 0): Option Nat :=
  match xs with
  | [] => none
  | a :: tail => if a == s then some start else indexOf? tail s (start+1)

def requiredArgument (name : String) : ReaderT Arguments (Except String) String := do
  let args ← read
  let value := match indexOf? args name with
    | some i => if i + 1 < args.length then args[i+1]! else ""
    | none => ""
  if value == "" then throw s!"Command line argument {name} missing"
  return value

def optionalSwitch (name : String) : ReaderT Arguments (Except String) Bool := do
  let args ← read
  return match (indexOf? args name) with
  | some _ => true
  | none => false

#eval requiredArgument "--input" |>.run ["--input", "foo"]
-- Except.ok "foo"

#eval requiredArgument "--input" |>.run ["foo", "bar"]
-- Except.error "Command line argument --input missing"

#eval optionalSwitch "--help" |>.run ["--help"]
-- Except.ok true

#eval optionalSwitch "--help" |>.run []
-- Except.ok false

/-!
Notice that `throw` was available from the inner `Except` monad. The cool thing is you can switch
this around and get the exact same result using `ExceptT` as the outer monad transformer and
`ReaderM` as the wrapped monad. Try changing requiredArgument to `ExceptT String (ReaderM Arguments) Bool`.

Note: the `|>.` notation is described in [Readers](readers.lean.md#the-reader-solution).

## Adding more layers

Here's the best part about monad transformers. Since the result of a monad transformer is itself a
monad, you can wrap it inside another transformer! Suppose you need to pass in some read only context
like the command line arguments, update some read-write state (like program Config) and optionally
throw an exception, then you could write this:

-/
structure Config where
  help : Bool := false
  verbose : Bool := false
  input : String := ""
  deriving Repr

abbrev CliConfigM := StateT Config (ReaderT Arguments (Except String))

def parseArguments : CliConfigM Bool := do
  let mut config ← get
  if (← optionalSwitch "--help") then
    throw "Usage: example [--help] [--verbose] [--input <input file>]"
  config := { config with
    verbose := (← optionalSwitch "--verbose"),
    input := (← requiredArgument "--input") }
  set config
  return true

def main (args : List String) : IO Unit := do
  let config : Config := { input := "default"}
  match parseArguments |>.run config |>.run args with
  | Except.ok (_, c) => do
    IO.println s!"Processing input '{c.input}' with verbose={c.verbose}"
  | Except.error s => IO.println s


#eval main ["--help"]
-- Usage: example [--help] [--verbose] [--input <input file>]

#eval main ["--input", "foo"]
-- Processing input file 'foo' with verbose=false

#eval main ["--verbose", "--input", "bar"]
-- Processing input 'bar' with verbose=true

/-!
In this example `parseArguments` is actually three stacked monads, `StateM`, `ReaderM`, `Except`. Notice
the convention of abbreviating long monadic types with an alias like `CliConfigM`.

## Monad Lifting

Lean makes it easy to compose functions that use different monads using a concept of automatic monad
lifting.  You already used lifting in the above code, because you were able to compose
`optionalSwitch` which has type `ReaderT Arguments (Except String) Bool` and call it from
`parseArguments` which has a bigger type `StateT Config (ReaderT Arguments (Except String))`.
This "just worked" because Lean did some magic with monad lifting.

To give you a simpler example of this, suppose you have the following function:
-/
def divide (x : Float ) (y : Float): ExceptT String Id Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    pure (x / y)

#eval divide 6 3 -- Except.ok 2.000000
#eval divide 1 0 -- Except.error "can't divide by zero"
/-!

Notice here we used the `ExceptT` transformer, but we composed it with the `Id` identity monad.
This is then the same as writing `Except String Float` since the identity monad does nothing.

Now suppose you want to count the number of times divide is called and store the result in some
global state:
-/

def divideCounter (x : Float) (y : Float) : StateT Nat (ExceptT String Id) Float := do
  modify fun s => s + 1
  divide x y

#eval divideCounter 6 3 |>.run 0    -- Except.ok (2.000000, 1)
#eval divideCounter 1 0 |>.run 0    -- Except.error "can't divide by zero"

/-!

The `modify` function is a helper which makes it easier to use `modifyGet` from the `StateM` monad.
But something interesting is happening here, `divideCounter` is returning the value of
`divide`, but the types don't match, yet it works?  This is monad lifting in action.

You can see this more clearly with the following test:

-/
def liftTest (x : Except String Float) :
  StateT Nat (Except String) Float := x

#eval liftTest (divide 5 1) |>.run 3 -- Except.ok (5.000000, 3)

/-!

Notice that `liftTest` returned `x` without doing anything to it, yet that matched the return type
`StateT Nat (Except String) Float`.  Monad lifting is provided by monad transformers.  if you
`#print liftTest` you will see that Lean is implementing this using a call to a function named
`monadLift` from the `MonadLift` type class:

```lean,ignore
class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α
```

So `monadLift` is a function for lifting a computation from an inner `Monad m α ` to an outer `Monad n α`.
You could replace `x` in `liftTest` with `monadLift x` if you want to be explicit about it.

The StateT monad transformer defines an instance of `MonadLift` like this:

```lean
@[inline] protected def lift {α : Type u} (t : m α) : StateT σ m α :=
  fun s => do let a ← t; pure (a, s)

instance : MonadLift m (StateT σ m) := ⟨StateT.lift⟩
```
This means that any monad `m` can be wrapped in a `StateT` monad by using the function
`fun s => do let a ← t; pure (a, s)` that takes state `s`, runs the inner monad action `t`, and
returns the result and the new state in a pair `(a, s)` without making any changes to `s`.

Because `MonadLift` is a type class, Lean can automatically find the required `monadLift`
instances in order to make your code compile and in this way it was able to find the `StateT.lift`
function and use it to wrap the result of `divide` so that the correct type is returned from
`divideCounter`.

If you have an instance `MonadLift m n` that means there is a way to turn a computation that happens
inside of `m` into one that happens inside of `n` and (this is the key part) usually *without* the
instance itself creating any additional data that feeds into the computation. This means you can in
principle declare lifting instances from any monad to any other monad, it does not, however, mean
that you should do this in all cases.  You can get a very nice report on how all this was done by
adding the line `set_option trace.Meta.synthInstance true in` before `divideCounter` and moving you
cursor to the end of the first line after `do`.

This was a lot of detail, but it is very important to understand how monad lifting works because it
is used heavily in Lean programs.

## Transitive lifting

There is also a transitive version of `MonadLift` called `MonadLiftT` which can lift multiple
monad layers at once.  In the following example we added another monad layer with
`ReaderT String ...` and notice that `x` is also automatically lifted to match.

-/
def liftTest2 (x : Except String Float) :
  ReaderT String (StateT Nat (Except String)) Float := x

#eval liftTest2 (divide 5 1) |>.run "" |>.run 3
-- Except.ok (5.000000, 3)

/-!

The ReaderT monadLift is even simpler than the one for StateT:

```lean,ignore
instance  : MonadLift m (ReaderT ρ m) where
  monadLift x := fun _ => x
```

This lift operation creates a function that defines the required `ReaderT` input
argument, but the inner monad doesn't know or care about `ReaderT` so the
monadLift function throws it away with the `_` then calls the inner monad action `x`.
This is a perfectly legal implementation of the `ReaderM` monad.

## Add your own Custom MonadLift

This does not compile:
-/
def main2 : IO Unit := do
  try
    let ret ← divideCounter 5 2 |>.run 0
    IO.println (toString ret)
  catch e =>
    IO.println e

/-!
saying:
```
typeclass instance problem is stuck, it is often due to metavariables
  ToString ?m.4786
```

The reason is `divideCounter` returns the big `StateT Nat (ExceptT String Id) Float` and that type
cannot be automatically lifted into the `main` return type of `IO Unit` unless you give it some
help.

The following custom `MonadLift` solves this problem:

-/
def liftIO (t : ExceptT String Id α) : IO α := do
  match t with
  | .ok r => EStateM.Result.ok r
  | .error s => EStateM.Result.error s

instance : MonadLift (ExceptT String Id) IO where
  monadLift := liftIO

def main3 : IO Unit := do
  try
    let ret ← divideCounter 5 2 |>.run 0
    IO.println (toString ret)
  catch e =>
    IO.println e

#eval main3 -- (2.500000, 1)
/-!

It turns out that the `IO` monad you see in your `main` function is based on the `EStateM.Result` type
which is similar to the `Except` type but it has an additional return value. The `liftIO` function
converts any `Except String α` into `IO α` by simply mapping the ok case of the `Except` to the
`Result.ok` and the error case to the `Result.error`.

## Lifting ExceptT

In the previous [Except](except.lean.md) section you saw functions that `throw` Except
values. When you get all the way back up to your `main` function which has type `IO Unit` you have
the same problem you had above, because `Except String Float` doesn't match even if you use a
`try/catch`.

-/

def main4 : IO Unit := do
  try
    let ret ← divide 5 0
    IO.println (toString ret)  -- lifting happens here.
  catch e =>
    IO.println s!"Unhandled exception: {e}"

#eval main4 -- Unhandled exception: can't divide by zero

/-!

Without the `liftIO` the `(toString ret)` expression would not compile with a similar error:

```
typeclass instance problem is stuck, it is often due to metavariables
  ToString ?m.6007
```

So the general lesson is that if you see an error like this when using monads, check for
a missing `MonadLift`.

## Summary

Now that you know how to combine your monads together, you're almost done with understanding the key
concepts of monads! You could probably go out now and start writing some pretty nice code! But to
truly master monads, you should know how to make your own, and there's one final concept that you
should understand for that. This is the idea of type "laws". Each of the structures you've learned
so far has a series of laws associated with it. And for your instances of these classes to make
sense, they should follow the laws! Check out [Monad Laws](laws.lean.md).
-/