/-
Tests that scoped instances work during Verso module docstring elaboration (#15817).

`{open X +scoped}` in a module docstring activates the scoped instances of `X` for the remainder of
that docstring (and nowhere else). Furthermore, elaborating a module docstring doesn't interfere
with scoped instances in declarations that are being elaborated concurrently. The `sleep`s in the
final test ensure that the docstring is still elaborating while the `by_cases` tactic runs. That
tactic expands to `open Classical in ...`. This arrangement deterministically reproduces #15817.
-/
import Lean

set_option doc.verso true

/-!
{open Classical +scoped}

With {name}`Classical.propDecidable` active: {lean}`fun (p : Prop) => if p then 1 else 0`
-/

/--
error: failed to synthesize instance of type class
  Decidable p

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
/-!
The instance activated in the previous module docstring is no longer active:
{lean}`fun (p : Prop) => if p then 1 else 0`
-/

theorem t0 (p : Prop) : True := by
  sleep 500
  by_cases h : p <;> trivial

/-!
The tactic block above elaborates concurrently with this module docstring.

```lean
#eval IO.sleep 2000
```
-/
