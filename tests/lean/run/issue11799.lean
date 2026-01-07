-- Reproducer for issue #11799
-- Panic in async elaboration for theorems with a docstring within `where`
import Lean

-- Main reproducer: theorem with docstring on where-bound auxiliary
theorem foo : True := aux where /-- doc -/ aux := True.intro

-- Variant: def with docstring (this always worked)
def bar : True := aux where /-- doc -/ aux := True.intro

-- Variant: multiple where-bound auxiliaries with docstrings
theorem baz : True ∧ True := ⟨aux1, aux2⟩ where
  /-- first aux -/ aux1 := True.intro
  /-- second aux -/ aux2 := True.intro

-- Verify the docstrings are actually attached
open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let check (name : Name) (expected : String) : MetaM Unit := do
    let some doc ← findDocString? env name
      | throwError "no docstring found for {name}"
    unless doc == expected do
      throwError "docstring mismatch for {name}: expected {repr expected}, got {repr doc}"
  check ``foo.aux "doc"
  check ``bar.aux "doc"
  check ``baz.aux1 "first aux"
  check ``baz.aux2 "second aux"
