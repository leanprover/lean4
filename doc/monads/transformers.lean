/-!
# Monad Transformers

In the previous sections you learned about some handy monads [Option](monads.lean.md),
[IO](monads.lean.md), [Reader](readers.lean.md), [State](states.lean.md) and
[Except](except.lean.md), and you now know how to make your function use one of these, but what you
do not yet know is how to make your function use multiple monads at once.

For example, suppose you need a function that wants to access some Reader state and optionally throw
an exception?  This would require composition of two monads `Reader` and `Except` and this is what
monad transformers are for.

A monad transformer is fundamentally a wrapper type. It is generally parameterized by another
monadic type. You can then run actions from the inner monad, while adding your own customized
behavior for combining actions in this new monad. The common transformers add `T` to the end of an
existing monad name. You will find `OptionT`, `ExceptT`, `ReaderT`, `StateT` but there is no transformer
for `IO`.  So generally if you need `IO` it becomes the innermost wrapped monad.

In the following example we use `ReaderT` to provide some read only state to our function
and this `ReaderT` transformer will wrap an `Except` monad.  If all goes well the
`requiredArgument` returns the value of a required argument and `optionalSwitch`
returns true if the optional argument is present.

-/
abbrev Arguments := List String

def List.posOf? (xs : List String) (s : String) (i := 0): Option Nat :=
  match xs with
  | [] => none
  | a :: tail => if a = s then some i else posOf? tail s (i+1)

def requiredArgument (name: String) : ReaderT Arguments (Except String) String := do
  let args ← read
  let value := match args.posOf? name with
  | some i => if i < args.length - 1 then args[i+1]! else ""
  | none => ""
  if value == "" then throw s!"Command line argument {name} missing"
  return value

def optionalSwitch (name: String) : ReaderT Arguments (Except String) Bool := do
  let args ← read
  return match (args.posOf? name) with
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
`Reader` as the wrapped monad. Try changing requiredArgument to `ExceptT String (Reader Arguments) Bool`.

## Adding more layers

Here's the best part about monad transformers. Since the result of a monad transformer is itself a
monad, you can wrap it inside another transformer! Suppose you need to pass in some read only state
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

def main (args: List String) : IO Unit := do
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
In this example `parseArguments` is actually 3 stacked monads, `State`, `Reader`, `Except`. Notice
the convention of abbreviating long monadic types with an alias like `CliConfigM`.

## Monad Lifting

Lean makes it easy to compose functions that use different monads using a concept of automatic monad
lifting.  You already used lifting in the above code, because you were able to compose
`optionalSwitch` which has type `ReaderT Arguments (Except String) Bool` and call it from
`parseArguments` which has a bigger type `StateT Config (ReaderT Arguments (Except String))`.
This "just worked" because Lean did some magic with monad lifting.

To give you a simpler example of this, suppose you have the following funciton:
-/
def divide (x: Float ) (y: Float): ExceptT String Id Float :=
  if y == 0 then
    throw "can't divide by zero"
  else
    pure (x / y)

#eval divide 6 3 -- Except.ok 2.000000
#eval divide 1 0 -- Except.error "can't divide by zero"
/-!

Notice here we used the `ExceptT` transformer, but we composed it with the `Id` identity monad.
This is then the same as writing `Except String Float` since the identity monad does nothing.

Now suppose we want to count the number of times we call divide and store the result in some
global state:
-/

def divideCounter (x:Float) (y:Float) : StateT Nat (ExceptT String Id) Float := do
  modify fun s => s + 1
  divide x y

#eval divideCounter 6 3 |>.run 0    -- Except.ok (2.000000, 1)
#eval divideCounter 1 0 |>.run 0    -- Except.error "can't divide by zero"

/-!

Here we used the `modify` helper which makes it easier to use `modifyGet` from the `StateM` monad.
But something interesting is happening here.  `divideCounter` is returning the value of
`divide`, but the types don't match, yet it works?  This is monad lifting in action.

You can see this more clearly with the following test:

-/
def liftTest (x : Except String Float) : StateT Nat (Except String) Float :=
  x

#eval liftTest (divide 5 1) |>.run 3 -- Except.ok (5.000000, 3)

/-!

Notice that `liftTest` returned `x` without doing anything to it, yet that matched the return type
`StateT Nat (Except String) Float`.  Monad lifting is done by our monad transformers.  if you
`#print liftTest` you will see that it is implementing this using a call to a function named
`monadLift` from the `MonadLiftT` type class.

The StateT monad transformer defines an instance of `MonadLift` like this:

```lean
@[inline] protected def lift {α : Type u} (t : m α) : StateT σ m α :=
  fun s => do let a ← t; pure (a, s)

instance : MonadLift m (StateT σ m) := ⟨StateT.lift⟩
```
This means that any monad `m` can be wrapped in a `StateT` monad by inventing the trivial function
`fun s => do let a ← t; pure (a, s)` that takes state `s`, runs the inner monad action `t`, and
returns the result and the new state in a pair `(a, s)` without making any changes to `s`.

Because `MonadLift` is a type class, type inference can automatically find the required `monadLift`
instances in order to make your code compile and in this way it was able to find the `StateT.lift`
function and use it to wrap the result of `divide` so that the correct type is returned from
`divideCounter`.

If we have an instance `MonadLiftT m n` that means there is a way to turn a computation that happens
inside of `m` into one that happens inside of `n` and (this is the key part) usually *without* the
instance itself creating any additional data that feeds into the computation. This means you can in
principle declare lifting instances from any monad to any other monad, it does not, however, mean
that you should do this in all cases.  You can get a report from Lean of how all this was done by
uncommenting the line `set_option trace.Meta.synthInstance true in` before main and moving the
cursor to the end of the first line after `do` and you will see a nice detailed report.

This was a lot of detail, but it is very important to understand how monad lifting works because it
is used heavily in Lean programs.

## Add your own Custom Lifting

-/
def main2 : IO Unit := do
  try
    let ret ← divideCounter 5 2 |>.run 0
    IO.println (toString ret)
  catch e =>
    IO.println e

/-!

This does not compile saying:
```
typeclass instance problem is stuck, it is often due to metavariables
  ToString ?m.4786
```

`divideCounter` returns the big `StateT Nat (ExceptT String Id) Float` and the problem is that
cannot be automatically transformed into the `main` return type of `IO Unit` unless we give it some
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

This instance makes it possible to lift the result of type `ExceptT String Id` into the type
required by main which is `IO Unit`. Fortunately this lift is relatively easy because IO is just an
alias for the `EStateM.Result` which is very similar to the `Except` object in that it also has an
`ok` or `error` state.

## Summary

Now that you know how to combine your monads together, you're almost done with understanding the key
concepts of monads! You could probably go out now and start writing some pretty nice code! But to
truly master monads, you should know how to make your own, and there's one final concept that you
should understand for that. This is the idea of type "laws". Each of the structures we've gone over
so far has a series of laws associated with it. And for your instances of these classes to make
sense, they should follow the laws! Check out [Monad Laws](laws.lean.md).
-/