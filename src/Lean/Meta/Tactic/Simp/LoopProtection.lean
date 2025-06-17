/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

def currentlyLoopChecking : SimpM Bool := do
  return !(← getContext).loopCheckStack.isEmpty

def getLoopCache (thm : SimpTheorem) : SimpM (Option LoopProtectionResult) := do
  return (← get).loopProtectionCache.lookup? thm

def setLoopCache (thm : SimpTheorem) (r : LoopProtectionResult) : SimpM Unit := do
  modifyThe State fun s => { s with loopProtectionCache := s.loopProtectionCache.insert thm r }

def setLoopCacheOkIfUnset (thm : SimpTheorem) : SimpM Unit := do
  unless (← getLoopCache thm).isSome do
    setLoopCache thm .ok

def setLoopCacheLoop (loop : Array SimpTheorem): SimpM Unit := do
  let thm := loop[0]!
  assert! (← getLoopCache thm).isNone
  assert! loop.size > 0
  setLoopCache thm (.loop loop)

@[inline] def withFreshUsedTheorems (x : SimpM α) : SimpM α := do
  let saved := (← get).usedTheorems
  modify fun s => { s with usedTheorems := {} }
  try x finally modify fun s => { s with usedTheorems := saved }

def mkLoopWarningMsg (thms : Array SimpTheorem) : SimpM MessageData := do
  let mut msg := m!""
  if thms.size = 1 then
    msg := msg ++ m!"Ignoring looping simp theorem: {← ppOrigin thms[0]!.origin}"
  else
    msg := msg ++ m!"Ignoring jointly looping simp theorems: \
      {.andList (← thms.mapM (ppOrigin ·.origin)).toList}"
  let mut others := #[]
  for other in (← get).usedTheorems.toArray do
    if thms.all (·.origin != other) then
      others := others.push other
  unless others.isEmpty do
    msg := msg ++ .note m!"These theorems may also play a role:
      {.andList (← others.mapM (ppOrigin ·)).toList}"

  msg := msg ++ .hint' m!"You can disable a simp theorem from the default simp set by \
    passing `- theoremName` to `simp`."
  msg := msg ++ .hint' m!"You can disable this check using `simp -loopProtection`."
  pure msg

private def rotations (a : Array α) : Array (Array α) := Id.run do
  let mut r : Array (Array α) := #[]
  for i in [:a.size] do
    r := r.push (a[i:] ++ a[:i])
  return r

/--
Check `thm` for loops. Called by the two entry points below.
-/
private def checkLoopCore (thm : SimpTheorem) : SimpM LoopProtectionResult := do
  -- Check or fill cache
  if let some r ← getLoopCache thm then
    return r
  else
    withTraceNode `Meta.Tactic.simp.loopProtection (fun _ => return m!"loop-checking {← ppSimpTheorem thm}") do
      -- Checking for a loop
      let seenThms := (← getContext).loopCheckStack
      if let some idx := seenThms.idxOf? thm then
        let loopThms := (seenThms.take (idx + 1)).toArray.reverse
        assert! loopThms[0]! == thm
        trace[Meta.Tactic.simp.loopProtection] "loop detected: {.andList (← loopThms.mapM (ppOrigin ·.origin)).toList}"
        (rotations loopThms).forM setLoopCacheLoop
      else
        -- Check the right-hand side
        withPushingLoopCheck thm do
        withFreshCache do
          let type ← inferType (← thm.getValue)
          forallTelescopeReducing type fun _xs type => do
            let rhs := (← whnf type).appArg!
            -- We ignore the simp result.
            -- A different design is possible where we use the simplified RHS to continue
            -- rewriting, but it would be a too severe change to `simp`’s semantics
            let _ ← simp rhs
            -- If we made it this far without finding a loop, this theorem is not looping
            -- Remember that to not try again
            setLoopCacheOkIfUnset thm

      -- No the cache should have been filled
      if let some r ← getLoopCache thm then
        return r
      else
        throwError "loop protection cache not filled for {(← ppOrigin thm.origin)}"


/--
Entry point into the loop protection mechanism from `Simp.Rewrite`: Called just
before `thm` is applied, and returns whether we should proceed.

This is used to cut loops while doing a loop check for another theorem.

It also used to be used to do lazy check of any rewritten theorem, but that was too expensive. Could
be added as an option, though.
-/
def checkRewriteForLoops (thm : SimpTheorem) : SimpM Bool := do
  let cfg ← getConfig
  -- No loop checking when disabled or in single pass mode
  if !cfg.loopProtection || cfg.singlePass then return true

  -- Permutating and local theorems are never checked, so accept when starting
  -- a loop check, and ignore when inside a loop check
  if thm.perm || thm.proof.hasFVar then
    return !(← currentlyLoopChecking)

  -- Now the cache tells us if this was looping
  if let .loop _thms ← checkLoopCore thm then
    -- Only when this is the starting point and we have not warned before: report the loop
    return false
  else
    return true

/--
Main entry point to the loop protection mechanis: Checks if the given theorem is looping in the
current simp set, and prints a warning if it does.

Assumes that `withRef` is set appropriately.
-/
def checkLoops (ctxt : Simp.Context) (methods : Methods) (thm : SimpTheorem) : MetaM Unit := do
  -- No loop checking when disabled or in single pass mode
  if !ctxt.config.loopProtection || ctxt.config.singlePass then return

  -- Permutating and local theorems are never checked, so accept when starting
  -- a loop check, and ignore when inside a loop check
  if thm.perm || thm.proof.hasFVar then return

  let _ ← SimpM.run ctxt (s := {}) (methods := methods) do
    if let .loop thms ← checkLoopCore thm then
      logWarning (← mkLoopWarningMsg thms)
