import Lean.Meta

/-!
Tests that `realizeConst` adds the realized constants to the kernel environment of the calling
branch without type checking them when `debug.skipKernelTC` is set there. `realize` always runs
with kernel checking disabled, and the realized constants used to be type checked when replayed into
each caller's kernel environment regardless of the caller's options.

The realization below adds a theorem whose value does not have its type, so the kernel rejects it
exactly when it checks the realized constants.
-/

open Lean Meta

def realizeIllTyped (constName : Name) : MetaM Unit :=
  realizeConst ``Nat.add constName do
    addDecl <| .thmDecl {
      name := constName, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }

/--
error: (kernel) declaration type mismatch, 'Nat.add.illTypedChecked' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
run_meta realizeIllTyped `Nat.add.illTypedChecked

set_option debug.skipKernelTC true in
#guard_msgs in
run_meta realizeIllTyped `Nat.add.illTypedUnchecked
