/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.While
public import Init.Data.Range.Polymorphic
namespace Lean.Util.ParamMinimizer
/-!
A very simple parameter minimizer.
-/

/-- Status of the parameter minimizer procedure. -/
public inductive Status where
  | /-- Has not found a solution. -/
    missing
  | /-- Found a non minimal solution. -/
    approx
  | /-- Found a precise solution. -/
    precise
  deriving Inhabited, Repr

/--
Result type for the parameter minimizer.
-/
public structure Result where
  /-- Search outcome (`missing`, `approx`, or `precise`) -/
  status    : Status
  /-- The final parameter bitmask. -/
  paramMask : Array Bool
  /-- Number of `test` invocations performed. -/
  numCalls  : Nat

structure Context (m : Type → Type) where
  /-- Initial parameter selection -/
  initialMask : Array Bool
  /--
  An expensive monotonic predicate for testing whether a given parameter
  configuration works or not.
  -/
  test        : Array Bool → m Bool
  /--
  Budget. That is, the maximum number of calls to `test` that we are willing to perform.
  `0` means unbounded.
  -/
  maxCalls    : Nat

structure State where
  cur      : Array Bool
  added    : Array Nat := #[]
  numCalls : Nat := 0
  found    : Bool := false

/-!
We use `throw ()` to interrupt the search.
-/

abbrev M (m : Type → Type) := ReaderT (Context m) (ExceptT Unit (StateT State m))

/--
Marks that a solution has been found. That is, we found a bitmask where
`test` returned `true`
-/
def markFound [Monad m] : M m Unit :=
  modify fun s => { s with found := true }

def incNumCalls [Monad m] : M m Unit :=
  modify fun s => { s with numCalls := s.numCalls + 1 }

/--
Adds parameter `i` to current set.
Sets bit `i` to `true` and records that it was added.
-/
def add (i : Nat) [Monad m] : M m Unit :=
  modify fun s => { s with
    added := s.added.push i
    cur := s.cur.set! i true
  }

/--
Removes parameter `i` from current set.
Sets bit `i` to `false`.
-/
def erase (i : Nat) [Monad m] : M m Unit :=
  modify fun s => { s with
    cur := s.cur.set! i false
  }

/--
Restores parameter `i` after an unsuccessful removal
Sets bit `i` back to `true`.
-/
def restore (i : Nat) [Monad m] : M m Unit :=
  modify fun s => { s with
    cur := s.cur.set! i true
  }

def tryCur [Monad m] : M m Bool := do
  let maxCalls := (← read).maxCalls
  if maxCalls > 0 && (← get).numCalls ≥ maxCalls then
    throw ()
  else
    modify fun s => { s with numCalls := s.numCalls + 1 }
    if (← (← read).test (← get).cur) then
      markFound (m := m)
      return true
    else
      return false

/--
**Initialization (growing phase).**
Starting from `initialMask`, this procedure sequentially activates parameters
(i.e., flips `false` bits to `true`) until `test` first returns `true`.

For each inactive parameter index `i`, it:
1. sets `cur[i] := true` and records `i` in `added`;
2. calls `tryCur` to evaluate the updated mask;
3. stops immediately once `test` succeeds.

This phase exploits the assumption that `test` is *monotonic* and that the
minimal true configuration is *close* to `initialMask`.  It guarantees that
at completion, the current mask `cur` satisfies `test` if there is a configuration
that satisfies it. `(← get).added.back!` is the element whose inclusion first made `test` true.
-/
def init [Monad m] : M m Unit := do
  let initialMask := (← read).initialMask
  for h : i in *...initialMask.size do
    unless initialMask[i] do
      add i
    if (← tryCur) then return

/--
**Pruning (minimization phase).**

Starting from a configuration `cur` known to satisfy `test`, this procedure
iterates through the indices stored in `added` **in reverse order**, removing
each one temporarily to check if it is necessary.

For each recorded index `i` (except the last one added, which is known to be
required since its removal made `test` fail during `init`):

1. sets `cur[i] := false`;
2. re-evaluates `tryCur`;
3. if `test` remains true, keeps `i` cleared;
   otherwise restores `cur[i] := true`.

After this phase, `cur` is guaranteed to be *1-minimal*: removing any single
`true` bit would make `test` return `false`.
-/
def prune [Monad m] : M m Unit := do
  -- **Note**: We skip the last added element because removing it
  -- would necessarily make `test` fail — that's the one that flipped it to true.
  let mut k := (← get).added.size - 1
  while k > 0 do
    k := k - 1
    let i := (← get).added[k]!
    erase i
    unless (← tryCur) do
      restore i

def main [Monad m] : M m Unit := do
  init
  if (← get).found then
    prune

/--
**Runs the parameter minimization procedure.**

Given an initial bitmask `initialMask` representing the active parameters,
and a monotonic predicate `test : Array Bool → m Bool`, this function searches
for the smallest (1-minimal) superset of `initialMask` that satisfies `test`.

Execution proceeds in two phases:

1. **`init`** – gradually activates parameters until `test` first succeeds;
2. **`prune`** – removes superfluous active parameters while preserving success.

If the search completes without exceeding `maxCalls`, the result is marked as
`.precise`.  If the budget is exceeded but a valid configuration was found,
the result is `.approx`.  If no configuration satisfies `test`, the result is
`.missing`.

`maxCalls = 0` disables the call budget limit.
-/
public def search
    [Monad m]
    (initialMask : Array Bool)
    (test : Array Bool → m Bool)
    (maxCalls : Nat := 0) -- 0 means unbounded
    : m Result := do
  if (← test initialMask) then
    return { paramMask := initialMask, numCalls := 1, status := .precise }
  let (r, s) ← main { initialMask, test, maxCalls} |>.run |>.run { cur := initialMask, numCalls := 1 }
  let status := if s.found then
    match r with
    | .ok _ => .precise
    | .error _ => .approx
  else
    .missing
  return { paramMask := s.cur, numCalls := s.numCalls, status }

end Lean.Util.ParamMinimizer
