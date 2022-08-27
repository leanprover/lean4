import Std.Data.HashMap
/-!
# State

In the [previous section](readers.lean.md), you learned about the Reader monad. Hopefully this gave you
a new perspective on Lean. It showed that, in fact, you _can_ have global variables of some sort;
you just need to encode them in the type signature somehow, and this is what monads are for! In this
part, we'll explore the `StateM` monad, which is like a `ReaderM` only the state can also be updated.

## Motivating example: Tic Tac Toe

For this part, we'll use a simple model for a Tic Tace Toe game. The main object is the `GameState`
data type containing several important pieces of information. First and foremost, it has the
"board", a map from 2D tile indices to the "Tile State" (X, O or empty). Then it also knows the
current player, and it has a random generator.
-/

open Std (HashMap)
abbrev TileIndex := Nat × Nat -- a 2D index

inductive TileState where
  | TileEmpty | TileX | TileO
  deriving Repr, BEq

inductive Player where
  | XPlayer | OPlayer
  deriving Repr, BEq

abbrev Board := HashMap TileIndex TileState

structure GameState where
  board : Board
  currentPlayer : Player
  generator : StdGen

/-!
Let's think at a high level about how some of our game functions would work. You could, for
instance, have a function for selecting a random move. This would output a `TileIndex` to play and
alter our game's number generator. You would then make a move based on the selected move and the
current player. This would change the board state as well as swap the current player. In other
words, we have operations that depend on the current state of the game, but also need to **update
that state**.

## The StateM Monad to the Rescue

This is exactly the situation the `StateM` monad deals with. The `StateM` monad wraps computations in
the context of reading and modifying a global state object.

It is parameterized by a single type parameter `s`, the state type in use. So just like the `ReaderM`
has a single type you read from, the `StateM` has a single type you can both **read from and write
to**. There are three primary actions you can take within the `StateM`monad:

- **get** - retrieves the state, like Reader.read
- **set** - updates the state
- **modifyGet** - retrieves the state, then updates it

There is also a `run` function, similar to `run` on `ReaderM`. Like the `ReaderM` monad, you must
provide an initial state, in addition to the computation to run. `StateM` then produces two outputs:
the result of our computation combined with the final updated state.

If you wish to discard the final state and just get the computation's result, you can use
`run'` method instead.  Yes in Lean, the apostraphe can be part of a name, you read this "run
prime", and the general naming convention is that the prime method discards something.

So for our Tic Tac Toe game, many of our functions will have a signature like `State GameState a`.

## Our Stateful Functions

Now we can examine some of the different functions mentioned above and determine their types. We
have for instance, picking a random move:

-/
open TileState

def findOpen (board: HashMap TileIndex TileState) : List TileIndex :=
  board.toList.filterMap fun (i, x) => guard (x == TileEmpty) *> pure i

def chooseRandomMove : StateM GameState TileIndex := do
  let game ← get
  let openSpots := findOpen game.board
  let gen := game.generator
  let (i, gen') := randNat gen 0 (openSpots.length - 1)
  set { game with generator := gen' }
  return openSpots[i]!

/-!
This returns a `TileIndex` and modifies the random number generator stored in our state!
Notice we have a fun little use of the `Applicative.seqRight` operator `*>` in `findOpen`
described in [Applicatives](applicatives.lean.md).

Now we can create the function that can make a move:
-/
open Player

def tileStateForPlayer : Player → TileState
| XPlayer => TileX
| OPlayer => TileO

def nextPlayer : Player →  Player
| XPlayer => OPlayer
| OPlayer => XPlayer

def applyMove (i: TileIndex): StateM GameState Unit := do
  let game ← get
  let p := game.currentPlayer
  let newBoard := game.board.insert i (tileStateForPlayer p)
  set { game with currentPlayer := nextPlayer p, board := newBoard }

/-!
This updates the board in the `GameState` with the new tile, and then changes the current player,
providing no output (`Unit` return type).

So finally, we can combine these functions together with `do` notation, and it actually looks quite
clean! We don't need to worry about the side effects. The different monadic functions handle them.
Here's a sample of what your function might look like to play one turn of the game. At the end, it
returns a boolean determining if we've filled all the spaces:
-/

def isGameDone : StateM GameState Bool := do
  let game ← get
  return (findOpen game.board).isEmpty

def nextTurn : StateM GameState Bool := do
  let i ← chooseRandomMove
  applyMove i
  isGameDone

/-!
To give you a quick test harness that runs all moves for both playes you can run this:
-/

instance : ToString TileState where
  toString p := match p with
    | TileEmpty => " "
    | TileX => "X"
    | TileO => "O"

def initBoard : Board := Id.run do
  let mut board := HashMap.empty
  for i in [0:3] do
    for j in [0:3] do
      let t : TileIndex := (i, j)
      board := board.insert t TileEmpty
  board

def printBoard (b: Board) : IO Unit :=
  for i in [0:3] do
    let mut row : List String := []
    for j in [0:3] do
      let x : TileIndex := (i, j)
      let s := b.find? x
      row := match s with
      | none => row
      | some tile => (row.append [toString tile])
    IO.println row

def main : IO Unit := do
  let gen ← IO.stdGenRef.get
  let (x, gen') := randNat gen 0 1
  let player := if x = 0 then XPlayer else OPlayer
  let mut gs : GameState := {
    board := initBoard,
    currentPlayer := player,
    generator := gen' }
  for _ in [0:9] do
    let (_, g) := nextTurn gs
    gs := g
  printBoard gs.board

#eval main
-- [X, X, O]
-- [X, O, O]
-- [O, O, X]

/-!

Note that when you run the above code interactively the random number generator always starts in the
same place.  But if you run `lean --run states.lean` then you will see randomness in the result.

## Implementation

It may be helpful to see how the `StateM` monad adds the input state and output state.  If you look
at the reduced Type for `nextTurn`:
-/
#reduce StateM GameState Bool
-- GameState → Bool × GameState
/-!

So a function like `nextTurn` that might have just returned a `Bool` has been modified by the
`State` monad such that the initial `GameState` is passed in as a new input argument, and the output
value has been changed to the pair `Bool × GameState` so that it can return the pure `Bool` and the
updated `GameState`.  This is why the call to nextTurn looks like this: `let (_, g) := nextTurn gs`.
This expression `(_, g)` conveniently breaks the pair up into 2 values, we don't care what the first
value is (so we use underscore `_`), but we do need the updated state `g` which we can then assign
back to our mutable `gs` variable to use next time around this loop.

## State, IO and other languages

When thinking about Lean, it is often seen as a restriction that we can't have global variables or
`static` variables like you can with other languages like Python or C++. However, hopefully you see
now this isn't true. You can have a data type with exactly the same functionality as a Python class.
You would simply have many functions that can modify some global state using the `StateM` monad.

The difference is in Lean we simply put a label on these types of functions. We don't allow it to
happen for free anywhere in an uncontrolled fashion because that results in too many sleepless
nights debugging nasty code.  We want to know when side effects can potentially happen, because
knowing when they can happen makes our code easier to reason about. In a Python class, many of the
methods won't actually need to modify the global state. But they could, which makes it harder to
debug them. In Lean we can simply make these pure functions, and the compiler will ensure they stay
pure and cannot modify any global state.

IO is the same way. It's not like we can't perform IO in Lean. Instead, we want to label the areas
where we can, to increase our certainty about the areas where we don't need to. When we know part of
our code cannot communicate with the outside world, we can be far more certain of its behavior.

The `StateM` monad is also a more disciplined way of managing side effects. Top level code could
call a `StateM` function multiple times with different independent initial states, even doing that
across multiple tasks in parallel and each of these cannot clobber the state belonging to other
tasks. Monadic code is more reusable than code that uses global variables.

## Summary

That wraps it up for the `StateM` monad! There is one more very useful monad that can be used to do
exception handling which we'll cover in the [next section](except.lean.md).

-/
