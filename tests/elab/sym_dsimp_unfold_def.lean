import Lean
/-!
Tests that `Sym.dsimp` unfolds definitions and rewrites with `rfl`-theorems provided as
parameters, like `Meta.dsimp` does with `dsimp [f]`.
-/

def f (a : Nat) := a + a

/--
trace: case grind
x : Nat
⊢ x + x = x + x
-/
#guard_msgs in
example (x : Nat) : f x = x + x := by
  sym =>
    dsimp [f]
    show_goals
    exact rfl

-- Non-recursive definition by pattern matching: the equational theorems `m.eq_1`/`m.eq_2`
-- are tried first, and `m.eq_def` unfolds the applications they do not cover.
def m (b : Bool) (x : Nat) : Nat :=
  match b with
  | true => x
  | false => 0

/--
trace: case grind
x : Nat
⊢ x = x
-/
#guard_msgs in
example (x : Nat) : m true x = x := by
  sym =>
    dsimp [m]
    show_goals
    exact rfl

/--
trace: case grind
b : Bool
x : Nat
⊢ (match b with
    | true => x
    | false => 0) =
    match b with
    | true => x
    | false => 0
-/
#guard_msgs in
example (b : Bool) (x : Nat) : m b x = match b with | true => x | false => 0 := by
  sym =>
    dsimp [m]
    show_goals
    exact rfl

-- Structural recursion: the equational theorems are proved by `rfl`.
def g : Nat → Nat
  | 0 => 1
  | n+1 => g n + 1

/--
trace: case grind
n : Nat
⊢ g n + 1 = g n + 1
-/
#guard_msgs in
example (n : Nat) : g (n + 1) = g n + 1 := by
  sym =>
    dsimp [g]
    show_goals
    exact rfl

-- Well-founded recursion: the equational theorems are not proved by `rfl`, so `dsimp` cannot
-- use them.
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
termination_by n => n

/-- error: `Sym.dsimp` made no progress -/
#guard_msgs in
example : fib 2 = 1 := by
  sym =>
    dsimp [fib]

-- `rfl`-theorems are accepted, other theorems are rejected.
/--
trace: case grind
x : Nat
⊢ x = x
-/
#guard_msgs in
example (x : Nat) : x + 0 = x := by
  sym =>
    dsimp [Nat.add_zero]
    show_goals
    exact rfl

/-- error: cannot use `Nat.zero_add` as a dsimp theorem, it is not proved by `rfl` -/
#guard_msgs in
example (x : Nat) : 0 + x = x := by
  sym =>
    dsimp [Nat.zero_add]

-- Definitions and `rfl`-theorems are also available in the `rewrite [...]` dsimproc DSL.
register_sym_dsimp unfoldF where
  post := ground >> rewrite [f, Nat.add_zero]

/--
trace: case grind
x : Nat
⊢ x + x = x + x
-/
#guard_msgs in
example (x : Nat) : f x + 0 = x + x := by
  sym =>
    dsimp unfoldF
    show_goals
    exact rfl
