/-!
# ST monad

In the previous sections, [StateM](states.lean.md) and [ReaderM](readers.lean.md), you saw how
`ReaderM` provides readonly state and `StateM` provides updatable state. There is another monad
called `ST` which stands for "State Transfomer" which is a _stateful computation_: the computation
is seen as transforming one state into another, where the new state will actually be constructed by
modifying the old state in place.

This is based on the work of John Launchbury and Simon L Peyton Jones in
[Lazy Functional State Threads](https://www.microsoft.com/en-us/research/wp-content/uploads/1994/06/lazy-functional-state-threads.pdf).

A state transfomer can be used as a first-class value which means it can be passed to a funciton,
returned as a result and stored in a data structure, which means you can store it in a `ReaderM`
context to make part of that context updatable.

## Motivating example: A simple Job Server

This simple server has a `ReaderT ServerContext` that contains a bunch of useful state needed by our
server function, but it also has a reference to an updateable `List Nat` which is typed as `IO.Ref
(List Nat)`. `IO.Ref` is an alias for `ST.Ref` which is a mutable reference to an object.

In this example the server will use multi-threading to process all the items in the `args` list in
parallel, and each `asyncProcess` will create a new thread and use the thread safe `ST.Ref.modify`
function to update the shared state, which is just a listed of `processed` jobs in our case.

-/
structure ServerContext where
   hIn : IO.FS.Stream
   hOut : IO.FS.Stream
   args : List Nat
   processed : IO.Ref (List Nat)

def asyncProcess (i: Nat) : ReaderT ServerContext IO (Task (Except IO.Error Unit)) := do
  let jobs ← read
  IO.asTask do
    IO.sleep 1
    jobs.processed.modify (λ s => i :: s)

def processTasks (args: List Nat) : ReaderT ServerContext IO Unit := do
  let tasks ← args.mapM fun s => asyncProcess s
  for task in tasks do
    ofExcept task.get

def server (args : List Nat) : IO (List Nat) := do
  let hIn ← IO.getStdin
  let hOut ← IO.getStdout
  let processedRef : IO.Ref (List Nat) ← IO.mkRef []
  let context : ServerContext := { hIn, hOut, args, processed := processedRef}
  processTasks args |>.run context
  context.processed.get
/-!

Notice the `server` creates the `ServerContext` as the `ReaderM` context and calls `processTasks` to
process the arg list.  Notice also that `asyncProcess` uses the `IO.asTask` function to create a new
thread to do the work. To simulate actual work and add some randomness it sleeps for 1 millisecond
then modifies the `processed` list in place by prepending it's work item `i` to the list.

You might be wondering whether this is violating the `ReaderT` contract that says the `ReaderT`
context is read only?  Well the trick is to think of the `IO.Ref` as a pointer to another object.
The pointer itself is not changing which keeps the `ReaderT` contract. It is what the pointer points
to that is changing, in this case a `List Nat` object.  As is shown in [Lazy Functional State
Threads](https://www.microsoft.com/en-us/research/wp-content/uploads/1994/06/lazy-functional-state-threads.pdf)
so long as access to this object is serialized in a single threaded way, it is safe to use this
pattern in a functional programming language.

Notice another important tid bit in the above code is the use of the `List.mapM` function.  This is
a monad aware version of `List.map` that runs the map lambda in the context of the given monad `m`.
In this way `asyncProcess` gets access to our `ReaderT ServerContext IO` monad. Try changing this to
`List.map` and you will see an interesting error.

To test this server we create an arg list containing 1000 work items using  `List.range workItems` then
run the server, then we have to sort the result because if you add an `IO.println` function on `x` you
will see that the resulting `processed` list is not in order because of the randomness of thread
scheduling.
-/
def test : IO Unit := do
  let workItems := 1000
  let x ← server (List.range workItems)

  let a := x.toArray.qsort (·<·)

  -- now make sure we got every result and that no multi-threaded clobbering of
  -- our shared state happened...
  for expected in List.range workItems do
    let actual := a[expected]!
    if actual ≠ expected then
      IO.println s!"unexpected {actual} instead of {expected}"

  IO.println "ok"

#eval timeit "running: " test

--ok
-- running:  512ms

/-!
This test executes 1000 threads and while each thread only sleeps for 1 millisecond it will take a
lot longer than 1 millisecond for all the threads to run depending on the overhead of thread
scheduling on your operating system where it has to wait for an available CPU core, etc.
This test also shows that the `ST.Ref.modify` function is thread safe.

## So which is best? StateM or ST.Ref ?

`StateM` updates are also very optimized in Lean because even though you seems to be creating a new
state every time you update it, the Lean compiler is able to reuse objects very efficiently so you
will not see a big performance benefit from using `ST.Ref`.

But in this particular multi-threading scenario it is easier to use `ST.Ref.modify` in the context
of `IO.asTask` than it is to use a `StateT` modify function because there is good `MonadLift`
support from `ST` to `EStateM` which is the result type for the IO monad.  You will learn
more about monad lifting in [Transformers](transformers.lean.md).

There is one more very useful monad that can be used to do exception handling which will be covered
in the [next section](except.lean.md).

-/
