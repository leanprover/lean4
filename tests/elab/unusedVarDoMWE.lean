module

import Init.Control.Do

/-!
Regression test: the new do elaborator should not produce false-positive
"unused variable" warnings for mutable variables reassigned inside `try`/`catch`.

The root cause was that `ControlStack.stateT.runInBase` packed mutable variables
into a state tuple without adding `TermInfo`, so the linter could not see that
the variables were used.
-/

set_option linter.unusedVariables true
set_option backward.do.legacy false

-- Mut in try/catch with branching reassignment
def test_mut_try_catch : IO Nat := do
  let mut params := 0
  for p in #[1, 2, 3] do
    try
      if p > 2 then
        params ← pure (params + 10)
      else
        params ← pure (params + p)
    catch _ =>
      pure ()
  return params

-- Mut with try reassign, catch returns
def test_mut_try_reassign (f : Nat → IO Nat) : IO Nat := do
  let mut proof ← f 0
  try proof ← f proof
  catch _ => return 0
  return proof

-- Tuple pattern mut reassign in for+try
def test_pat_reassign_try : IO Nat := do
  let mut g' := 0
  for x in #[1, 2, 3] do
    try
      (_, g') ← pure (x, g' + x)
    catch _ => g' ← pure g'
  return g'
