import Lean

/-!
Tests the `MonadMacroAdapter CoreM` instance, which allows running `MacroM` actions via `liftMacroM`
directly in `CoreM` and, through lifting, in `MetaM`.
-/

open Lean Elab

macro "double% " x:term : term => `($x + $x)

/-- info: some (1 + 1) -/
#guard_msgs in
#eval show CoreM Unit from do
  let stx? ← liftMacroM <| expandMacro? (← `(double% 1))
  logInfo m!"{stx?}"

/-!
The next macro scope must be threaded through `CoreM`: separate `liftMacroM` calls and `CoreM`'s own
`withFreshMacroScope` must all produce distinct names.
-/

/-- info: [true, true, true] -/
#guard_msgs in
#eval show CoreM Unit from do
  let a ← liftMacroM <| withFreshMacroScope <| Macro.addMacroScope `x
  let b ← liftMacroM <| withFreshMacroScope <| Macro.addMacroScope `x
  let c ← withFreshMacroScope <| MonadQuotation.addMacroScope `x
  logInfo m!"{[a != b, a != c, b != c]}"

/-- error: oops -/
#guard_msgs in
#eval show CoreM Unit from do
  liftMacroM (Macro.throwError "oops" : MacroM Unit)

/-- info: some (2 + 2) -/
#guard_msgs in
run_meta do
  let stx? ← liftMacroM <| expandMacro? (← `(double% 2))
  logInfo m!"{stx?}"

/-- info: true -/
#guard_msgs in
run_meta do
  let a ← liftMacroM <| withFreshMacroScope <| Macro.addMacroScope `x
  let b ← liftMacroM <| withFreshMacroScope <| Macro.addMacroScope `x
  logInfo m!"{a != b}"

/-! `TermElabM` has a shortcut instance instead of going through the lifting instance. -/

/-- info: Term.instMonadMacroAdapterTermElabM -/
#guard_msgs in
#synth MonadMacroAdapter Term.TermElabM
