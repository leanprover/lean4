/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Basic
public import Std.Tactic.BVDecide.Syntax
import Lean.Meta.Sym.Simp.NNF
import Lean.Meta.Sym.Simp.Prenex
import Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps
import Lean.Meta.Tactic.BVDecide.Main
import Lean.Meta.Tactic.Grind.Main
public import Lean.Meta.Tactic.BVDecide.TacticContext
import Lean.Meta.Sym.Apply
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Intro
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Sym.SynthInstance

namespace Lean.Meta.Tactic

namespace Epr

open BVDecide Normalize

open Sym.Internal in
/--
Introduce `Nonempty` instances for as many type parameters as possible in the local context.
This is potentially useful for skolemization.
-/
def addNonempty (g : MVarId) : Sym.SymM Unit := do
  g.withContext do
    let mut todo : Std.HashSet FVarId := {}
    for decl in ← getLCtx do
      if decl.isImplementationDetail || decl.isLet then continue
      let type ← Sym.instantiateMVarsS decl.type
      if let .sort (.succ u) := type then
        let query ← mkAppS (← mkConstS ``Nonempty [.succ u]) (← Sym.share decl.toExpr)
        if (← Sym.synthInstance? query).isNone then
          todo := todo.insert decl.fvarId
      else if let .fvar typeId := type then
        if todo.contains typeId then
          let type ← mkFVarS typeId
          let lvl ← Sym.getLevel type
          let instType ← mkAppS (← mkConstS ``Nonempty [lvl]) type
          let inst ← mkAppS₂ (← mkConstS ``Nonempty.intro [lvl]) type (← Sym.share decl.toExpr)
          Sym.registerInstance instType inst
          todo := todo.erase typeId

/--
Convert all `hyps` to NNF.
-/
def nnf (hyps : Array Hyp) (cfg : BVDecide.TacticContext) : Sym.SymM (Array Hyp) :=
  let methods := { pre := Sym.Simp.nnf }
  Sym.Simp.SimpM.run' (methods := methods) (config := { maxSteps := cfg.config.maxSteps }) do
    hyps.mapM fun hyp => do
      let res ← Sym.Simp.simp hyp.type
      hyp.applySimpResult res

/--
Split up potential top level conjunctions in `hyps` and return them as multiple separate hypotheses.
-/
partial def andFlatten (hyps : Array Hyp) : Sym.SymM (Array Hyp) := do
  hyps.flatMapM fun hyp => flattenOne [hyp]
where
  flattenOne (worklist : List Hyp) (acc : Array Hyp := #[]) : Sym.SymM (Array Hyp) := do
    match worklist with
    | [] => return acc
    | hyp :: worklist =>
      match_expr hyp.type with
      | And lhs rhs =>
        let lhsHyp := {
          hyp with
            type := lhs,
            value := mkApp3 (mkConst ``And.left) lhs rhs hyp.value
            source := .andFlattened hyp.source
        }
        let rhsHyp := {
          hyp with
            type := rhs,
            value := mkApp3 (mkConst ``And.right) lhs rhs hyp.value
            source := .andFlattened hyp.source
        }
        flattenOne (lhsHyp :: rhsHyp :: worklist) acc
      | _ => flattenOne worklist (acc.push hyp)


/--
Prenexing procedure for a hyp that contains an existential. Here we minscope, then pull existentials,
then finally pull foralls.
-/
def prenexWithExists (hyp : Hyp) (cfg : BVDecide.TacticContext) : Sym.SymM Hyp := do
  let cfg := { maxSteps := cfg.config.maxSteps }
  let hyp ← hyp.applySimpResult <| ← Sym.simp (methods := { pre := Sym.Simp.minscope }) (config := cfg) hyp.type
  let hyp ← hyp.applySimpResult <| ← Sym.simp (methods := { pre := Sym.Simp.pullExists }) (config := cfg) hyp.type
  let hyp ← hyp.applySimpResult <| ← Sym.simp (methods := { pre := Sym.Simp.pullForall }) (config := cfg) hyp.type
  return hyp

/--
Prenexing procedure for a hyp that does not contain an existential. Here we just pull the foralls up
right away.
-/
def prenexWithoutExists (hyp : Hyp) (cfg : BVDecide.TacticContext) : Sym.SymM Hyp := do
  let cfg := { maxSteps := cfg.config.maxSteps }
  let hyp ← hyp.applySimpResult <| ← Sym.simp (methods := { pre := Sym.Simp.pullForall }) (config := cfg) hyp.type
  return hyp

def skolemize (g : MVarId) (hyp : Hyp) : Sym.SymM (MVarId × Hyp) := do
  let mut g := g
  let mut hyp := hyp
  while true do
    match ← skolemStep g hyp with
    | some (g', hyp') =>
      g := g'
      hyp := hyp'
    | none => break
  return (g, hyp)
where
  skolemStep (g : MVarId) (hyp : Hyp) : Sym.SymM (Option (MVarId × Hyp)) := g.withContext do
    let_expr Exists α q := hyp.type | return none
    let lvl ← Sym.getLevel α
    let rule ← Sym.mkBackwardRuleFromExpr (mkApp4 (mkConst ``Exists.elim [lvl]) α q (mkConst ``False) hyp.value)
    let [g] ← rule.apply' g | unreachable!
    let .goal #[_skolem, newHyp] g ← Sym.introN g 2 | unreachable!
    g.withContext do
      let type ← newHyp.getType
      let newHyp := {
        name := hyp.name
        type := type
        value := mkFVar newHyp
        source := hyp.source
      }
      return some (g, newHyp)

end Epr

public def epr (g : MVarId) (cfg : BVDecide.TacticContext) : MetaM Unit := g.withContext do
  let params ← Grind.mkDefaultParams {}
  Grind.GrindM.run (params := params) do
    let (hyps, g) ← BVDecide.Normalize.collectMVarHyps g
    Epr.addNonempty g
    g.withContext do
      let hyps ← Epr.nnf hyps cfg
      let hyps ← Epr.andFlatten hyps
      let mut finalHyps := Array.emptyWithCapacity hyps.size
      let mut g := g
      for hyp in hyps do
        if hyp.type.find? (fun e => e.isConstOf ``Exists) |>.isSome then
          let (g', hyp) ← g.withContext do
            let hyp ← Epr.prenexWithExists hyp cfg
            let r ← Epr.skolemize g hyp
            return r
          g := g'
          finalHyps := finalHyps.push hyp
        else
          let hyp ← g.withContext do
            Epr.prenexWithoutExists hyp cfg
          finalHyps := finalHyps.push hyp
      let target := .hypTarget g finalHyps
      discard <| BVDecide.bvDecide target cfg

end Lean.Meta.Tactic
