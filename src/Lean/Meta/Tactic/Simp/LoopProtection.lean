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

def unlessWarnedBefore (thm : SimpTheorem) (k : SimpM Unit) : SimpM Unit := do
  unless (← get).loopProtectionCache.warned thm do
    modifyThe State fun s => { s with loopProtectionCache := s.loopProtectionCache.setWarned thm }
    k

def mkLoopWarningMsg (thms : Array SimpTheorem) : SimpM MessageData := do
  let mut msg := m!""
  if thms.size = 1 then
    msg := msg ++ m!"Ignoring looping simp theorem: {← ppOrigin thms[0]!.origin}"
  else
    msg := msg ++ m! "Ignoring jointly looping simp theorems: \
      {.andList (← thms.mapM (ppOrigin ·.origin)).toList}"
  msg := msg ++ .hint' m!"You can disable a simp theorem from the default simp set by \
    passing `- theoremName` to `simp`."
  msg := msg ++ .hint' m!"You can disable this check using `simp -loopProtection`."
  pure msg

private def rotations (a : Array α) : Array (Array α) := Id.run do
  let mut r : Array (Array α) := #[]
  for i in [:a.size] do
    r := r.push (a[i:] ++ a[:i])
  return r

def checkLoops (thm : SimpTheorem) : SimpM Bool := do
  let cfg ← getConfig
  -- No loop checking when disabled or in single pass mode
  if !cfg.loopProtection || cfg.singlePass then return true


  -- Permutating and local theorems are never checked, so accept when starting
  -- a loop check, and ignore when inside a loop check
  if thm.perm || thm.proof.hasFVar then
    return !(← currentlyLoopChecking)

  -- Check cache
  if (← getLoopCache thm).isNone then
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
          -- We ignore the result for now. We could return it to `tryTheoremCore` to avoid
          -- re-simplifying the right-hand side, but that would require some more refactoring
          let _ ← simp rhs
          -- If we made it this far without finding a loop, this theorem is fine
          setLoopCacheOkIfUnset thm

  -- Now the cache tells us if this was looping
  if let some (.loop thms) ← getLoopCache thm then
    -- Only when this is the starting point and we have not warned before: report the loop
    unless (← currentlyLoopChecking) do
      unlessWarnedBefore thm do
        if let .stx _ ref := thm.origin then
          logWarningAt ref (← mkLoopWarningMsg thms)
        else
          logWarning (← mkLoopWarningMsg thms)
    return false
  else
    return true
