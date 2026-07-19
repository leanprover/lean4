import Lean

/-!
A local declaration whose user name is `Name.anonymous` breaks name resolution for the
entire local context: `resolveLocalName` resolves an identifier by stripping trailing
components and searching the local context for the remaining prefix, and this stripping
bottoms out at `Name.anonymous`.  Thus, a local declaration named `Name.anonymous`
matches *every* identifier, shadowing all global constants.  The delaborator
(`delabConst`) then cannot find any name that round-trips for any constant, and renders
all of them as inaccessible (e.g., `True✝`).

`mkSimpleThunkType` used to create its binder with `Name.anonymous`.  The `match`
compiler uses it to create the minor premises of parameterless alternatives, and
tactics that introduce these binders using their binder name (e.g., `grind`) ended up
with a corrupted local context.  See issue #13773.
-/

open Lean Meta

/-- info: with anonymous binder: True✝ -/
#guard_msgs in
run_meta do
  -- Negative control: a binder named `Name.anonymous` introduced into the local
  -- context makes even the constant `True` unreferenceable.
  let bad := Expr.forallE .anonymous (mkConst ``Unit) (mkConst ``True) .default
  forallTelescope bad fun _ _ => do
    logInfo m!"with anonymous binder: {mkConst ``True}"

/-- info: with mkSimpleThunkType: True -/
#guard_msgs in
run_meta do
  -- `mkSimpleThunkType` must not use `Name.anonymous` for its binder.
  let thunk := mkSimpleThunkType (mkConst ``True)
  forallTelescope thunk fun _ _ => do
    logInfo m!"with mkSimpleThunkType: {mkConst ``True}"
