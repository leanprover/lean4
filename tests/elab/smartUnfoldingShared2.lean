module

/-!
Smart unfolding (`Meta.smartUnfoldingReduce?`) must not traverse the arguments of the
function it unfolds. Here they are shared terms whose tree size is exponential in their size
as a DAG: `dup n p` reduces to a pair whose two fields share the previous ones, so the fields of
`dup 22 (0, 1)` are trees of millions of nodes. Traversing them as trees allocates without
checking `maxHeartbeats`, and runs out of memory for larger `n` (e.g. 24).
-/

def dup : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n+1, p => match dup n p with
    | (a, b) => (a + b, b + a)

/-- The `if` before the `match` is reduced by smart unfolding, with `p` in its condition. -/
def loop (l : List Nat) (p : Nat × Nat) : Nat :=
  if p.2 = 7 then 0 else
  match l with
  | [] => p.1
  | n :: xs => match dup n p with
    | (a, b) => loop xs (a, b)

set_option maxHeartbeats 1000 in
example : loop [22] (0, 1) = 2^21 := by decide

/-- The accumulator grows as a DAG in each step, and is in the condition of the `if`. -/
def acc (l : List Nat) (p : Nat × Nat) : Nat :=
  if p.2 = 1000000 then 0 else
  match l with
  | [] => p.1
  | x :: xs => acc xs (p.1 + x, p.2 + p.1)

set_option maxHeartbeats 1000 in
example : acc (List.replicate 30 1) (0, 0) = 30 := by decide

/-!
The alternatives of a `match` of the body applied to more arguments than the `match` binds, and
lets and lambdas of the body.
-/

def overApplied : Nat → Nat → Nat
  | 0, y => y
  | k+1, y => (match k with
    | 0 => fun z => z + 1
    | j+1 => fun z => overApplied j z * 2) (y + k)

/-- info: 28 -/
#guard_msgs in
#eval overApplied 4 3

example : overApplied 4 3 = 28 := by decide
example : overApplied 4 3 = 28 := rfl

def withLet : List Nat → Nat → Nat
  | [], a => a
  | x :: xs, a =>
    let b := a + x
    (fun c => withLet xs (c + b)) a

/-- info: 19 -/
#guard_msgs in
#eval withLet [1, 2, 3] 1

example : withLet [1, 2, 3] 1 = 19 := by decide
example : withLet [1, 2, 3] 1 = 19 := rfl
