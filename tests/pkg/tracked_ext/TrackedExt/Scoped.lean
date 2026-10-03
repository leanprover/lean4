import TrackedExt.Ext

/-!
Scope operations on a generation-tracked scoped extension bump `Environment.trackedGen` exactly
when they change the entries in effect: activating a namespace with entries, and popping a scope that received
local entries, entries of a namespace activated in it, or other state modifications.
-/

open Lean

def gen (env : Environment) : Nat := env.trackedGen

/--
info: push +0, activate empty +0, activate +1, pop +1, state [1]
---
info: push +0, local entry +1, pop +1
---
info: push, pop +0
---
info: push, modify +1, pop +1, state []
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env := trackedScopedExt.addScopedEntry (← getEnv) `Foo 1
  let env₁ := trackedScopedExt.pushScope env
  let env₂ := trackedScopedExt.activateScoped env₁ `Bar
  let env₃ := trackedScopedExt.activateScoped env₂ `Foo
  let env₄ := trackedScopedExt.popScope env₃
  logInfo m!"push +{gen env₁ - gen env}, activate empty +{gen env₂ - gen env₁}, \
    activate +{gen env₃ - gen env₂}, pop +{gen env₄ - gen env₃}, \
    state {trackedScopedExt.getState env₃}"
  let env₅ := trackedScopedExt.pushScope env₄
  let env₆ := trackedScopedExt.addLocalEntry env₅ 2
  let env₇ := trackedScopedExt.popScope env₆
  logInfo m!"push +{gen env₅ - gen env₄}, local entry +{gen env₆ - gen env₅}, \
    pop +{gen env₇ - gen env₆}"
  let env₈ := trackedScopedExt.popScope (trackedScopedExt.pushScope env₇)
  logInfo m!"push, pop +{gen env₈ - gen env₇}"
  let env₉ := trackedScopedExt.pushScope env₈
  let env₁₀ := trackedScopedExt.modifyState env₉ (3 :: ·)
  let env₁₁ := trackedScopedExt.popScope env₁₀
  logInfo m!"push, modify +{gen env₁₀ - gen env₉}, pop +{gen env₁₁ - gen env₁₀}, \
    state {trackedScopedExt.getState env₁₁}"
