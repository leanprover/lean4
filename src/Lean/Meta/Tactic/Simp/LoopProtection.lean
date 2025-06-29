/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.Tactic.Simp.Types
import Lean.Linter.Basic

namespace Lean.Meta.Simp

register_builtin_option linter.loopingSimpArgs : Bool := {
  defValue := false
  descr := "\
    When enabled, `simp` will check if the theorems passed as simp arguments (`simp [thm1]`) \
    are possibly looping in the current simp set.\n\
    \n\
    More precisely, it tries to simplify the right-hand side of the theorem and complains if \
    that fails, which it typically does because of running out of recursion depth.\n\
    \n\
    This is a relatively expensive check, so it i disabled by default, and only run after \
    a `simp` call actually failed with a recursion depth error."

}

@[inline] def withFreshUsedTheorems (x : SimpM α) : SimpM α := do
  let saved := (← get).usedTheorems
  modify fun s => { s with usedTheorems := {} }
  try x finally modify fun s => { s with usedTheorems := saved }

private def ppOrigins (origins : Array Origin) : MetaM MessageData := do
  return .andList (← origins.mapM (return m!"`{← ppOrigin ·}`")).toList

def mkLoopWarningMsg (thm : SimpTheorem) : SimpM MessageData := do
  let mut msg := m!""
  msg := msg ++ m!"Possibly looping simp theorem: `{← ppOrigin thm.origin}`"

  let mut others := #[]
  for other in (← get).usedTheorems.toArray do
    if other != thm.origin  then
      others := others.push other
  unless others.isEmpty do
    msg := msg ++ .note m!"Possibly caused by: {← ppOrigins others}"

  msg := msg ++ .hint' m!"You can disable a simp theorem from the default simp set by \
    passing `- theoremName` to `simp`."
  pure msg

def shouldCheckLoops (force : Bool) (ctxt : Simp.Context) : CoreM Bool := do
  if ctxt.config.singlePass then return false
  if force then return true
  return linter.loopingSimpArgs.get (← getOptions)

/--
Main entry point to the loop protection mechanis: Checks if the given theorem is looping in the
current simp set, and logs a warning if it does.

Assumes that `withRef` is set appropriately for the warning.

With `force := off`, only runs when `linter.loopingSimpArgs` is enabled and presents it as a
linter. With `force := on` (typically after `simp` threw an exception) it prints plain warnings.
-/
def checkLoops (force : Bool) (ctxt : Simp.Context) (methods : Methods) (thm : SimpTheorem) : MetaM Unit := do
  -- No loop checking when disabled or in single pass mode
  unless (← shouldCheckLoops force ctxt) do return

  -- Ignore theorems depending on the local context for now
  if thm.proof.hasFVar then return

  let type ← inferType (← thm.getValue)
  forallTelescopeReducing type fun _xs type => do
    let rhs := (← whnf type).appArg!

      let _ ← SimpM.run ctxt (s := {}) (methods := methods) do
        -- We ignore the simp result.
        -- A different design is possible where we use the simplified RHS to continue
        -- rewriting, but it would be a too severe change to `simp`’s semantics
        tryCatchRuntimeEx do
            let _ ← simp rhs
          fun ex => do
            trace[Meta.Tactic.simp.loopProtection] "loop protection for {← ppOrigin thm.origin}: got exception{indentD ex.toMessageData}"
            if force then
              logWarning (← mkLoopWarningMsg thm)
            else
              Linter.logLint linter.loopingSimpArgs (← getRef) (← mkLoopWarningMsg thm)
