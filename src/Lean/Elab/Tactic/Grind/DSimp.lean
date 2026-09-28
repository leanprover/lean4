/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lean.Elab.Tactic.Grind.Basic
import Lean.Elab.Tactic.Grind.DSimprocDSL
import Lean.Meta.Sym.DSimp.Variant
import Lean.Meta.Sym.DSimp.Reduce
import Lean.Meta.Sym.DSimp.DSimproc
import Lean.Meta.Sym.DSimp.Rewrite
namespace Lean.Elab.Tactic.Grind
open Meta
open Sym.DSimp

def elabDSimpArgs (args? : Option (Array (TSyntax [`token.«*», `ident]))) : GrindTacticM DSimpArgs := do
  let some args := args? | return {}
  let mut fvarIds := #[]
  let mut zetaDeltaAll := false
  let mut declNames := #[]
  let lctx ← getLCtx
  for arg in args do
    if arg.raw.getKind == `ident then
      if let some decl := lctx.findFromUserName? arg.raw.getId then
        fvarIds := fvarIds.push decl.fvarId
      else
        declNames := declNames.push (← realizeGlobalConstNoOverload arg.raw)
    else
      zetaDeltaAll := true
  if !fvarIds.isEmpty && zetaDeltaAll then
    throwError "invalid `dsimp` arguments, local declarations and `*` have been provided"
  return { fvarIds, zetaDeltaAll, declNames }

/--
Adds the `dsimp` arguments to `methods`: local declarations are unfolded in `pre`, and the
global declarations (definitions to unfold and `rfl`-theorems) are handled in `post`.
-/
def addDSimpArgs (methods : Sym.DSimp.Methods) (args : DSimpArgs) : GrindTacticM Sym.DSimp.Methods := do
  let mut pre := methods.pre
  if args.zetaDeltaAll then
    pre := pre >> zetaDeltaAll
  unless args.fvarIds.isEmpty do
    pre := pre >> zetaDelta (FVarIdSet.ofArray args.fvarIds)
  let mut post := methods.post
  unless args.declNames.isEmpty do
    post := post >> (← Decls.ofNames args.declNames).toDSimproc
  return { pre, post }

def mkDSimpDefaultMethods (args : DSimpArgs) : GrindTacticM Sym.DSimp.Methods := do
  let pre  := beta >> dsimpProj >> dsimpMatch
  let post := evalGround
  addDSimpArgs { pre, post } args

def trivialDSimproc : DSimproc := fun _ =>
  return .rfl

def elabOptDSimproc (stx? : Option Syntax) : GrindTacticM DSimproc := do
  let some stx := stx? | return trivialDSimproc
  elabSymDSimproc stx

def elabDSimpVariant (variantName : Name) (args : DSimpArgs) : GrindTacticM (Sym.DSimp.Methods × Sym.DSimp.Config) := do
  if variantName.isAnonymous then
    return (← mkDSimpDefaultMethods args, {})
  let some v := Sym.DSimp.getSymDSimpVariant? (← getEnv) variantName
    | throwError "unknown Sym.dsimp variant `{variantName}`"
  let pre ← elabOptDSimproc v.pre?
  let post ← elabOptDSimproc v.post?
  return (← addDSimpArgs { pre, post } args, v.config)

@[builtin_grind_tactic Parser.Tactic.Grind.symDSimp] def evalSymDSimp : GrindTactic := fun stx => withMainContext do
  ensureSym
  let `(grind| dsimp $[$variantId?]? $[[ $[$args],* ]]?) := stx | throwUnsupportedSyntax
  let variantName := variantId?.map (·.getId) |>.getD .anonymous
  let args ← elabDSimpArgs args
  let cacheKey : DSimpCacheKey := { variant := variantName, args }
  let dsimpState := (← get).cache.dsimpState[cacheKey]?.getD {}
  let (methods, config) ← elabDSimpVariant variantName args
  let goal ← getMainGoal
  let (result, dsimpState) ← liftGrindM <| goal.withContext do
    Sym.DSimp.DSimpM.run (Sym.DSimp.dsimp (← goal.mvarId.getType)) methods config dsimpState
  modify fun s => { s with cache.dsimpState := s.cache.dsimpState.insert cacheKey dsimpState }
  match result with
  | .rfl _  => throwError "`Sym.dsimp` made no progress"
  | .step target' _ =>
    if target'.isTrue then
      goal.mvarId.assign (mkConst ``True.intro)
      replaceMainGoal []
    else
      let decl ← goal.mvarId.getDecl
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar target' decl.userName
      goal.mvarId.assign mvarNew
      replaceMainGoal [{ goal with mvarId := mvarNew.mvarId! }]

end Lean.Elab.Tactic.Grind
