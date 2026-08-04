/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Elab.Tactic.BVDecide.BVCheck
import Lean.Meta.Tactic.BVDecide.LRAT.Trim

public section

/-!
This module contains the implementation of `bv_decide?`.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace BVTrace

open Std.Tactic.BVDecide.LRAT
open Lean.Meta.Tactic
open Lean.Meta.Tactic.BVDecide

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

def mkContext (cfg : BVDecideConfig) : TermElabM TacticContext := do
  let lratPath ← getLratFileName
  BVCheck.mkContext lratPath cfg

inductive TraceResult where
  | normalize
  | check (path : System.FilePath)

def evalBvTrace (g : MVarId) (ctx : TacticContext) : Meta.Sym.SymM TraceResult := do
  let trace ← g.withContext do
    bvDecide g { ctx with config := { ctx.config with trimProofs := false } }
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
    return .normalize
  | some .. =>
    if ctx.config.trimProofs then
      let proof ← loadLRATProof ctx.lratPath
      let trimmed ← IO.ofExcept <| LRAT.trim proof
      dumpLRATProof ctx.lratPath trimmed ctx.config.binaryProofs
    let some lratFile := ctx.lratPath.fileName | throwError "could not find file name"
    return .check lratFile

open Lean.Meta.Tactic in
open Lean.Meta.Tactic.BVDecide in
@[builtin_tactic Lean.Parser.Tactic.bvTrace]
def evalBvTraceTactic : Tactic := fun
  | `(tactic| bv_decide?%$tk $cfgStx:optConfig) => do
    ensureBvDecide
    let cfg ← elabBVDecideConfig cfgStx
    let ctx ← mkContext cfg
    let g ← getMainGoal
    Meta.Sym.SymM.run do
      match ← evalBvTrace g ctx with
      | .normalize =>
        let normalizeStx ← `(tactic| bv_normalize $cfgStx:optConfig)
        TryThis.addSuggestion tk normalizeStx (origSpan? := ← getRef)
      | .check lratFile =>
        let bvCheckStx ← `(tactic| bv_check $cfgStx:optConfig $(quote lratFile.toString))
        TryThis.addSuggestion tk bvCheckStx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end BVTrace
end Lean.Elab.Tactic.BVDecide
