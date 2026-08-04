/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Elab.Tactic.BVDecide.BVDecide
public import Lean.Meta.Tactic.TryThis
import Lean.Meta.Tactic.BVDecide.TacticContext
import Lean.Meta.Tactic.BVDecide.Normalize
import Lean.Meta.Sym.Util

public section

/-!
This modules provides the implementation of `bv_check`.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace BVCheck

open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect
open Meta.Tactic.BVDecide

/--
Get the directory that contains the Lean file which is currently being elaborated.
-/
def getSrcDir : TermElabM System.FilePath := do
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of `{srcPath}`"
  return srcDir

def mkContext (lratPath : System.FilePath) (cfg : BVDecideConfig) : TermElabM TacticContext := do
  let lratPath := (← getSrcDir) / lratPath
  TacticContext.new lratPath cfg

@[inherit_doc Lean.Parser.Tactic.bvCheck]
def bvCheck (g : MVarId) (hypotheses : Array Normalize.Hyp) (ctx : TacticContext) :
    Meta.Sym.SymM Unit := do
  M.run (hypotheses := hypotheses) do
    discard <| closeWithBVReflection g (lratChecker ctx)

def evalBvCheck (g : MVarId) (ctx : TacticContext) (warn : MetaM Unit) :
    Meta.Sym.SymM Unit := do
  Normalize.PreProcessM.run' ctx.config g do
    if ← Normalize.bvNormalize then
      warn
    else
      bvCheck (← Normalize.PreProcessM.getGoal) (← Normalize.PreProcessM.getHyps) ctx

open Lean.Meta.Tactic in
@[builtin_tactic Lean.Parser.Tactic.bvCheck]
def evalBvCheckTactic : Tactic := fun
  | `(tactic| bv_check%$tk $cfgStx:optConfig $path:str) => do
    ensureBvDecide
    let cfg ← elabBVDecideConfig cfgStx
    let ctx ← mkContext path.getString cfg
    let g ← getMainGoal
    Meta.Sym.SymM.run <| evalBvCheck g ctx do
      let bvNormalizeStx ← `(tactic| bv_normalize $cfgStx)
      logWarning m!"This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."
      TryThis.addSuggestion tk bvNormalizeStx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end BVCheck
end Lean.Elab.Tactic.BVDecide
