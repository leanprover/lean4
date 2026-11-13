import Std
import Lean

open Lean Compiler

/-!
Checks that every declaration in `Init`, `Std` and `Lean` that is replaced by a `@[csimp]` theorem
is `noncomputable`, so we never compile against the wrong version.

Recursors and structure projections cannot be marked `noncomputable`; they are exempt.
-/

def csimpComputableDecls : CoreM (Array Name) := do
  let env ← getEnv
  let mut bad := #[]
  for (declName, _) in (CSimp.ext.getState env).map.toList do
    let some modIdx := env.getModuleIdxFor? declName | continue
    unless env.header.moduleNames[modIdx]!.getRoot matches `Init | `Std | `Lean do continue
    if isNoncomputable env declName then continue
    if (← getConstInfo declName) matches .recInfo _ then continue
    if env.isProjectionFn declName then continue
    bad := bad.push declName
  return bad.qsort Name.lt

/-- info: #[] -/
#guard_msgs in
#eval csimpComputableDecls

/-! Sanity check: the imported `@[csimp]` theorems are visible to the check. -/

/-- info: true -/
#guard_msgs in
#eval show CoreM _ from do
  let s := CSimp.ext.getState (← getEnv)
  return [``List.map, ``List.foldr, ``Array.instDecidableEq].all s.map.contains
