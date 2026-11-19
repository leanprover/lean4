module

prelude

public import Lean.DefEqAttrib
import Init.Data.Nat.Basic

/-!
# Can `@[defeq]` inference have `strict=true` while `validateDefEqAttr` throws?

The algorithm in `inferDefEqAttr` swallows `validateDefEqAttr` errors when
`strict` passed:

```
try withExporting ... validateDefEqAttr declName
catch e =>
  unless strict do logError m!"..."
```

This guards a theoretical case where the strict check (`.instances` transparency,
smart-unfolding ON, under `withoutExporting`) passes but the permissive check
(`.default`/`.all`, smart-unfolding OFF, under `withExporting` for public decls)
fails. The two differ along three axes: transparency, export-view, smart-unfolding.

Trying to construct a case:

1. Public `@[reducible] def hidden := 42` + public `theorem h = 42 := rfl`:
   Both strict and permissive fail. The `@[reducible]` marker apparently attaches
   to the exported view and does not make `hidden` instance-reducible under
   `withoutExporting`. Not a counterexample.

2. The same pair as private: strict=true, permissive=true. Both pass.

3. Recursive `@[reducible]` def relying on smart unfolding: same pattern — public
   fails both, private passes both.

Under the module system, it seems the `withoutExporting` in `inferDefEqAttr` does
not give the strict check a strictly-bigger view than the permissive check has.
Every case where strict succeeds, permissive succeeds too. The `unless strict do
logError` branch is therefore a defensive guard that (as far as this demonstrates)
is unreachable in practice.
-/

@[reducible] public def hidden : Nat := 42

-- Public version: error message from `validateDefEqAttr` surfaces via
-- `unless strict do logError` because strict=false (reducibility of the exported
-- view is gone under `withoutExporting`).
/--
error: Not a definitional equality: the left-hand side
  hidden
is not definitionally equal to the right-hand side
  42

Note: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.
-/
#guard_msgs in
public theorem test_public : hidden = 42 := rfl

-- Private version: both strict and permissive checks pass, tagged `@[defeq]`.
theorem test_private : hidden = 42 := rfl

/-- info: @[defeq] private theorem test_private : hidden = 42 -/
#guard_msgs in
#print sig test_private
