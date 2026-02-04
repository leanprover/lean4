/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
public import Lean.Elab.Command
meta import Lean.Elab.Command
import all Lean.Environment

open Lean Meta Elab Command

meta def optimizeProof (lb up : Option Nat) (n : Name) : CoreM Unit := do
  let .thmInfo thmInfo ← getConstInfo n
    | throwError "optimizeProof can only be applied to theorems"

  let decl' := .thmDecl { thmInfo with name := `tmp }
  let kenv := (← getEnv).toKernelEnv
  let diagEnv := kenv.resetDiag.enableDiag true
  let opts ← getOptions
  let hb1 ← IO.getNumHeartbeats
  match diagEnv.addDecl opts decl' none with
  | .error e => throwError "failed to recheck unmodified declaration:\n{e.toMessageData (← getOptions)}"
  | .ok diagEnv =>
    let hb2 ← IO.getNumHeartbeats
    let unfoldings := diagEnv.diagnostics.unfoldCounter.toArray
    logInfo m!"re-typechecking {.ofConstName n} took {hb2 - hb1} heartbeats, with {unfoldings.size} different unfoldings "
    let unfoldings := unfoldings.extract (lb.getD 0) (up.getD unfoldings.size)
    for (unfoldName, count) in unfoldings.take 160 do
      IO.println s!"Trying {unfoldName}..."
      -- logInfo m!"found {.ofConstName unfoldName} to be unfolded {_count} times; trying with that being opaque..."
      let decl ← getConstVal unfoldName
      let opaqueDecl := .axiomInfo { decl with isUnsafe := false }
      -- We always add to map₁, as the kernel uses find?' which checks map₁ first.
      let kenv' := { kenv with constants.map₁ := kenv.constants.map₁.insert unfoldName opaqueDecl }
      let hb1' ← IO.getNumHeartbeats
      match kenv'.addDecl opts decl' none with
      | .error _ =>
        -- logInfo m!"failed to recheck with {.ofConstName unfoldName} opaque"
        pure ()
      | .ok _ =>
        let hb2' ← IO.getNumHeartbeats
        logInfo m!"typechecking with {.ofConstName unfoldName} opaque ({count} unfoldings avoided) \
          succeeded in {hb2' - hb1'} heartbeats ({(1 - (hb2' - hb1').toFloat / (hb2 - hb1).toFloat)*100}% speedup)"


meta def elabOptimizeProof (lb ub : Option (TSyntax `num)) (n : Ident) : CommandElabM Unit := do
  Elab.Command.liftCoreM do
    withoutExporting do
      optimizeProof (lb.map (·.raw.toNat)) (ub.map (·.raw.toNat))
        (← resolveGlobalConstNoOverload n)

syntax "#optimizeProof " optional("[" optional(num) ":" optional(num) "] ") ident : command

elab_rules : command
  | `(#optimizeProof $n:ident) => elabOptimizeProof none none n
  | `(#optimizeProof [$[$lb]?:$[$ub]?] $n:ident) => elabOptimizeProof lb ub n


-- open Lean.Grind in
-- theorem test {α} [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α)
--   (Δ40 : d^2 * (d + t - d * t - 2) *
--     (d + t + d * t) = 0)
--   (Δ41 : -d^4 * (d + t - d * t - 2) *
--     (2 * d + 2 * d * t - 4 * d * t^2 + 2 * d * t^4 + 2 * d^2 * t^4 - c * (d + t + d * t)) = 0)
--   (_ : d * d_inv = 1)
--   (_ : (d + t - d * t - 2) * PSO3_inv = 1) :
--   t^2 = t + 1 := by grind

-- #optimizeProof test._proof_1_1
