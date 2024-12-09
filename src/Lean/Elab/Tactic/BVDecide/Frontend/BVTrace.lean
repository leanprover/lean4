/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide
import Lean.Elab.Tactic.BVDecide.Frontend.BVCheck
import Lean.Elab.Tactic.BVDecide.LRAT.Trim
import Lean.Meta.Tactic.TryThis
import Std.Tactic.BVDecide.Syntax

/-!
This module contains the implementation of `bv_decide?`.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.BVTrace


-- TODO: think of a more maintainable file pattern for this stuff.
/--
Produce a file with the pattern:
LeanFileName-DeclName-Line-Col.lrat
-/
def getLratFileName : TermElabM System.FilePath := do
  let some baseName := System.FilePath.mk (← getFileName) |>.fileName | throwError "could not find file name"
  let some declName ← Term.getDeclName? | throwError "could not find declaration name"
  let pos := (← getFileMap).toPosition (← getRefPos)
  return s!"{baseName}-{declName}-{pos.line}-{pos.column}.lrat"

open Std.Tactic.BVDecide.LRAT in
open Lean.Meta.Tactic in
open Lean.Elab.Tactic.BVDecide.LRAT in
@[builtin_tactic Lean.Parser.Tactic.bvTrace]
def evalBvTrace : Tactic := fun
  | `(tactic| bv_decide?%$tk $cfgStx:optConfig) => do
    let cfg := { (← elabBVDecideConfig cfgStx) with trimProofs := false }
    let lratFile : System.FilePath ← BVTrace.getLratFileName
    let ctx ← BVCheck.mkContext lratFile cfg
    let g ← getMainGoal
    let trace ← g.withContext do
      bvDecide g ctx
    /-
    Ideally trace.lratCert would be the `ByteArray` version of the proof already and we just write
    it. This isn't yet possible so instead we do the following:
    1. Produce the proof in the tactic.
    2. Skip trimming it in the tactic.
    3. Run trimming on the LRAT file that was produced by the SAT solver directly, emitting the
       correct binary format according to `sat.binaryProofs`.
    TODO: Fix this hack:
    1. Introduce `ByteArray` literals to the kernel.
    2. Just return the fully trimmed proof in the format desired by the configuration from `bvDecide`.
    3. Write it to the file directly.
    -/
    match trace.lratCert with
    | none =>
      let normalizeStx ← `(tactic| bv_normalize)
      TryThis.addSuggestion tk normalizeStx (origSpan? := ← getRef)
    | some .. =>
      if ctx.config.trimProofs then
        let lratPath := (← BVCheck.getSrcDir) / lratFile
        let proof ← loadLRATProof lratPath
        let trimmed ← IO.ofExcept <| trim proof
        dumpLRATProof lratPath trimmed cfg.binaryProofs
      let bvCheckStx ← `(tactic| bv_check $cfgStx:optConfig $(quote lratFile.toString))
      TryThis.addSuggestion tk bvCheckStx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end Frontend.BVTrace
end Lean.Elab.Tactic.BVDecide
