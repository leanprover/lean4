module

prelude

public import Lean.DefEqAttrib
import Init.Data.Nat.Basic

/-!
# `[defeq]` strict-only behavior

The `[defeq]` attribute requires the equation to hold at instance transparency.
The `[backward_defeq]` attribute is permissive (default/all transparency).
-/

@[reducible] public def hidden : Nat := 42

-- Public version: `[defeq]` validation runs `withExporting` view, where the
-- `@[reducible]` attribute on `hidden` is not visible, so the strict check fails.
/--
error: Not a definitional equality at instance transparency: the left-hand side
  hidden
is not definitionally equal to the right-hand side
  42
at the transparency used by `dsimp`

Note: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.
-/
#guard_msgs in
@[defeq] public theorem test_public : hidden = 42 := rfl

-- Private version: under `withoutExporting`, `@[reducible]` attaches and the
-- strict check passes; tagged `[defeq]`.
@[defeq] theorem test_private : hidden = 42 := rfl

/-- info: @[defeq] private theorem test_private : hidden = 42 -/
#guard_msgs in
#print sig test_private
