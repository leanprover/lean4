/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow
import Lean.Meta.Tactic.Ext
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Util

/-!
This module contains the implementation of the pre processing pass for automatically splitting up
structures containing information about supported types into individual parts recursively.

The implementation operates on all "interesting" types where a type is interesting if it is a non
recursive structure and at least one of the following conditions hold:
- it contains something of type `BitVec`/`UIntX`/`IntX`/`Bool`
- it is parametrized by an interesting type
- it contains another interesting type

For these it:
1. Iterates over all variables in the local context that have an interesting type. For these it
   recursively asserts all of the contained hypotheses as local facts
2. It post-processes with a custom simp-set that:
   - runs `ext_iff` lemmas if available in order to handle equality on structures
   - runs simprocs to bubble applications of projections onto control flow operators such as `ite`
     or `cond` into the control flow
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

structure ProjInfo where
  /-- Pre computed arity of the projection -/
  arity : Nat
  /-- Given proj (ctor.mk x1 x2 ... xn)  which xi do we reduce to -/
  offset : Nat
  /--
  Name of the accompanying constructor
  -/
  ctorName : Name

def projCtorProc (projFns : Std.HashMap Name ProjInfo) (ctors : Std.HashMap Name Nat) :
    Sym.Simp.Simproc := fun e => do
  e.withApp fun fn args => do
    let .const fn _ := fn | return .rfl
    let some projInfo := projFns[fn]? | return .rfl
    unless args.size == projInfo.arity do return .rfl
    let structArg := args.back!
    structArg.withApp fun structFn structArgs => do
      let .const structFn _ := structFn | return .rfl
      unless structFn == projInfo.ctorName do return .rfl
      let some ctorArity := ctors[structFn]? | return .rfl
      unless ctorArity == structArgs.size do return .rfl
      let result := structArgs[projInfo.offset]!
      return .step result (← mkEqRefl result)

/--
Add simp lemmas that we want to apply to structures that we find interesting to `simprocs` and
`theorems`.
-/
public def addStructureSimpLemmas (methods : Sym.Simp.Methods) :
    PreProcessM Sym.Simp.Methods := do
  let mut extTheorems : Sym.Simp.Theorems := {}
  let mut projFns := {}
  let mut projFnIndex := {}
  let mut ctorIndex := {}
  let interesting := (← PreProcessM.getTypeAnalysis).interestingStructures
  let env ← getEnv
  for const in interesting do
    let constInfo ← getConstInfoInduct const
    let ctor := constInfo.ctors.head!
    let ctorArity := (← getConstVal ctor).type.getForallArity
    ctorIndex := ctorIndex.insert ctor ctorArity
    for extIffThm in ← findExtIffThms constInfo do
      trace[Meta.Tactic.bv] m!"Using ext_iff: {extIffThm}"
      extTheorems := extTheorems.insert (← Sym.Simp.mkTheoremFromDecl extIffThm)
    let structInfo := getStructureInfo env const
    let fields := structInfo.fieldNames.size
    for proj in 0...fields do
      let some projFn := structInfo.getProjFn? proj | continue
      let arity := (← getConstVal projFn).type.getForallArity
      projFns := projFns.insert projFn
      projFnIndex := projFnIndex.insert projFn {
        arity,
        offset := proj + constInfo.numParams
        ctorName := ctor
      }
  return { methods with
    post := methods.post >> extTheorems.rewrite
    pre := methods.pre
      >> applyIteSimproc projFns
      >> applyCondSimproc projFns
      >> projCtorProc projFnIndex ctorIndex
  }
where
  findExtIffThms (info : InductiveVal) : MetaM (Array Name) := do
    let pat ← mkConstAppWithMVars info.name
    let thms ← Ext.getExtTheorems pat
    let env ← getEnv
    return thms.filterMap fun thm => Id.run do
      let .str root s := thm.declName | return none
      let extIffThm := .str root (s ++ "_iff")
      unless env.contains extIffThm do return none
      return some extIffThm

  /--
  Constructs `declName ?m.1 ?m.2 ...` as a synthetic discr tree pattern for ext theorems associated
  with `declName`.
  -/
  mkConstAppWithMVars (declName : Name) : MetaM Expr := do
    let c ← mkConstWithFreshMVarLevels declName
    let (mvars, _, _) ← forallMetaTelescopeReducing (← inferType c)
    return mkAppN c mvars

public partial def structuresPass : Pass where
  name := `structures
  run' := do
    let interesting := (← PreProcessM.getTypeAnalysis).interestingStructures
    if interesting.isEmpty then return false
    let goal ← PreProcessM.getTargetMVarId
    goal.withContext do
      let mut worklist := #[]
      for decl in ← getLCtx do
        if decl.isLet || decl.isImplementationDetail then
          continue
        let .const const us := decl.type.getAppFn | continue
        if interesting.contains const then
          worklist := worklist.push (← Sym.share (mkFVar decl.fvarId), const, us, decl.type.getAppArgs)

      let mut newHyps : Array Hyp := #[]
      let env ← getEnv
      while h : 0 < worklist.size do
        let (value, structConst, us, params) := worklist.back
        worklist := worklist.pop
        let fields := (getStructureInfo env structConst).fieldNames.size
        let constInfo ← getConstInfoInduct structConst
        let ctorInfo ← getConstInfoCtor constInfo.ctors.head!
        for proj in 0...fields do
          let projValue ← Sym.share <| ← mkProjFn ctorInfo us params proj value
          let projType ← Sym.inferType projValue
          if ← Meta.isProp projType then
            newHyps := newHyps.push {
              name := `h
              type := projType
              value := projValue
              source := .structureProjection projValue
            }
          else
            let .const const us := projType.getAppFn | continue
            if interesting.contains const then
              worklist := worklist.push (projValue, const, us, projType.getAppArgs)

      PreProcessM.addHyps newHyps
      postprocess goal
where
  postprocess (goal : MVarId) : PreProcessM Bool := do
    goal.withContext do
      let mut methods : Sym.Simp.Methods := {}
      methods ← addStructureSimpLemmas methods
      methods ← addDefaultTypeAnalysisLemmas methods
      let cfg ← PreProcessM.getConfig
      let config := {
        maxSteps := cfg.maxSteps
      }

      PreProcessM.mapSimpHyps methods config

end Normalize
end Lean.Meta.Tactic.BVDecide
