/-!
Tests that compiled code for `withPtrEq` skips the continuation if and only if the arguments are
pointer-equal.
-/

structure Point where
  x : Nat
  y : Nat
  deriving DecidableEq

-- Allocates a fresh object on each call.
@[noinline] def mkPoint (x : Nat) : IO Point := pure ⟨x, x + 1⟩

@[noinline] def eqPoint (a b : Point) : Bool :=
  withPtrEq a b (fun _ => dbgTrace "called k" fun _ => decide (a = b)) decide_eq_true

inductive Vec : Nat → Type where
  | nil : Vec 0
  | cons {n : Nat} (x : String) (xs : Vec n) : Vec (n + 1)
  deriving DecidableEq

@[noinline] def mkVec (x : String) : IO (Vec 2) := pure (.cons x (.cons x .nil))

@[noinline] def eqVec (n : Nat) (a b : Vec n) : Bool :=
  withPtrEq a b (fun _ => dbgTrace "called k" fun _ => decide (a = b)) decide_eq_true

-- Output goes to stderr only, so that it is not reordered relative to `dbgTrace`.
def main : IO Unit := do
  let p ← mkPoint 1
  let q ← mkPoint 1
  let r ← mkPoint 2
  IO.eprintln s!"{eqPoint p p}"
  IO.eprintln s!"{eqPoint p q}"
  IO.eprintln s!"{eqPoint p r}"
  let u ← mkVec "a"
  let v ← mkVec "a"
  IO.eprintln s!"{eqVec 2 u u}"
  IO.eprintln s!"{eqVec 2 u v}"
