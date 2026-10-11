import Lean

/-!
Test the `@[attribute]` attribute, which registers a `Lean.AttributeImpl`
constant as a custom attribute without requiring an `initialize` block.
-/

open Lean

/-- A simple custom attribute that just logs the declaration it's applied to. -/
@[attribute] def myCustomAttr : AttributeImpl where
  name := `myCustomAttr
  descr := "a test custom attribute"
  applicationTime := .afterTypeChecking
  add := fun decl _stx _kind => do
    logInfo m!"myCustomAttr applied to `{decl}`"

/-- info: myCustomAttr applied to `foo` -/
#guard_msgs in
@[myCustomAttr] def foo := 42

/-- info: myCustomAttr applied to `bar` -/
#guard_msgs in
@[myCustomAttr] def bar := "hello"

/-!
The custom attribute should be visible via `getAttributeImpl` / `isAttribute`.
-/

run_meta do
  unless isAttribute (← getEnv) `myCustomAttr do
    throwError "myCustomAttr is not a registered attribute"

/-!
Re-registering the same attribute name should be rejected.
-/

def myCustomAttr' : AttributeImpl where
  name := `myCustomAttr  -- collides with the one above
  descr := "duplicate"
  add := fun _ _ _ => pure ()

/--
error: Invalid attribute declaration: `myCustomAttr` has already been registered
-/
#guard_msgs in
attribute [attribute] myCustomAttr'

/-!
Tagging a declaration that isn't an `AttributeImpl` should be rejected.
-/

def notAnAttribute : Nat := 0

/--
error: Unexpected attribute implementation type: `{.ofConstName declName}` is not of type `Lean.AttributeImpl`
-/
#guard_msgs in
attribute [attribute] notAnAttribute

/-!
Local/scoped registration should be rejected.
-/

def anotherAttr : AttributeImpl where
  name := `anotherAttr
  descr := "another"
  add := fun _ _ _ => pure ()

/--
error: Invalid attribute scope: Attribute `[attribute]` must be global, not `local`
-/
#guard_msgs in
attribute [local attribute] anotherAttr
