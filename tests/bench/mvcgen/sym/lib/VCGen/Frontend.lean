/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Elab
public import Lean.Meta
public import Lean.Parser
public meta import Lean.Elab
public meta import Lean.Meta
public meta import Lean.Meta.Tactic.Grind.Main
public meta import Lean.Meta.Tactic.Grind.Solve
meta import Lean.Elab.Tactic.Grind
public meta import VCGen.Context
public meta import VCGen.Driver

open Lean Parser Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

/-!
`mvcgen'` tactic frontend: parse the user-facing argument syntax into a
`VCGen.Context`, run `VCGen.main`, and replace the main goal with the
resulting invariants and VCs.
-/

namespace VCGen

/--
Parse the optional `[...]` argument list for `mvcgen'`, partitioning entries into
spec theorems and simp lemmas. Follows the same approach as
`Lean.Elab.Tactic.Do.VCGen.mkSpecContext`: each entry is first tried as a spec theorem,
and on failure falls back to a simp/unfold lemma processed via `mkSimpContext`.
-/
public meta def mkSpecContext (lemmas : Syntax) (ignoreStarArg := false) : TacticM VCGen.Context := do
  let mut specThms ← getSpecTheorems
  let mut simpStuff := #[]
  let mut starArg := false
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``simpErase then
      try
        -- Try to interpret as a spec theorem erasure; fall back to simp erasure.
        let specThm ←
          if let some fvar ← Term.isLocalIdent? arg[1] then
            mkSpecTheoremFromLocal fvar.fvarId!
          else
            let id := arg[1]
            if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
              mkSpecTheoremFromConst declName
            else
              withRef id <| throwUnknownConstant id.getId.eraseMacroScopes
        specThms := specThms.erase specThm.proof
      catch _ =>
        simpStuff := simpStuff.push ⟨arg⟩ -- simp tracks its own erase stuff
    else if arg.getKind == ``simpLemma then
      unless arg[0].isNone && arg[1].isNone do
        -- When there is ←, →, ↑ or ↓ then this is for simp
        simpStuff := simpStuff.push ⟨arg⟩
        continue
      let term := arg[2]
      match ← Term.resolveId? term (withInfo := true) <|> Term.elabCDotFunctionAlias? ⟨term⟩ with
      | some (.const declName _) =>
        try
          let thm ← mkSpecTheoremFromConst declName
          specThms := specThms.insert thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | some (.fvar fvar) =>
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := specThms.insert thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | _ => withRef term <| throwError "Could not resolve spec theorem `{term}`"
    else if arg.getKind == ``simpStar then
      starArg := true
      simpStuff := simpStuff.push ⟨arg⟩
    else
      throwUnsupportedSyntax
  -- Build a simp context from the collected simp/unfold arguments, seeded with the
  -- spec simp theorems database (which contains `@[spec]`-registered simp equations
  -- and definitions to unfold).
  let stx ← `(tactic| simp +unfoldPartialApp -zeta [$(Syntax.TSepArray.ofElems simpStuff),*])
  let res ← mkSimpContext stx.raw
    (eraseLocal := false)
    (simpTheorems := getSpecSimpTheorems)
    (ignoreStarArg := ignoreStarArg)
  let simpThms := res.ctx.simpTheorems[0]?.getD {}
  -- Add local spec hypotheses when `*` is used.
  if starArg && !ignoreStarArg then
    let fvars ← getPropHyps
    for fvar in fvars do
      unless specThms.isErased (.local fvar) do
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := specThms.insert thm
        catch _ => continue
  let entailsConsIntroRule ← mkBackwardRuleFromDecl ``SPred.entails_cons_intro
  let entailsNilPureIntroRule ← mkBackwardRuleFromDecl ``SPred.entails_nil_pure_intro
  let entailsNilIntroRule ← mkBackwardRuleFromDecl ``SPred.entails_nil_intro
  let applyPureConsEntailsLRule ← mkBackwardRuleFromDecl ``SPred.apply_pure_cons_entails_l
  let applyPureConsEntailsRRule ← mkBackwardRuleFromDecl ``SPred.apply_pure_cons_entails_r
  let downPureIntroRule ← mkBackwardRuleFromDecl ``SPred.down_pure_intro
  let pureElimRule ← mkBackwardRuleFromDecl ``SPred.pure_elim'
  let pureIntroRule ← mkBackwardRuleFromDecl ``SPred.pure_intro
  let postCondEntailsRflRule ← mkBackwardRuleFromDecl ``PostCond.entails.rfl
  let postCondEntailsMkRule ← mkBackwardRuleFromDecl ``PostCond.entails.mk
  let exceptCondsEntailsRflRule ← mkBackwardRuleFromDecl ``ExceptConds.entails.rfl
  let exceptCondsEntailsPureRule ← mkBackwardRuleFromDecl ``ExceptConds.entails.pure
  let exceptCondsEntailsFalseRule ← mkBackwardRuleFromDecl ``ExceptConds.entails_false
  let exceptCondsEntailsTrueRule ← mkBackwardRuleFromDecl ``ExceptConds.entails_true
  let tripleOfEntailsWPRule ← mkBackwardRuleFromDecl ``Triple.of_entails_wp
  let andIntroRule ← mkBackwardRuleFromDecl ``And.intro
  let specThmsNew ← SymM.run <| migrateSpecTheoremsDatabase specThms simpThms
  return {
    specThms := specThmsNew,
    entailsConsIntroRule,
    entailsNilPureIntroRule,
    entailsNilIntroRule,
    applyPureConsEntailsLRule,
    applyPureConsEntailsRRule,
    downPureIntroRule,
    pureElimRule,
    pureIntroRule,
    postCondEntailsRflRule,
    postCondEntailsMkRule,
    exceptCondsEntailsRflRule,
    exceptCondsEntailsPureRule,
    exceptCondsEntailsFalseRule,
    exceptCondsEntailsTrueRule,
    tripleOfEntailsWPRule,
    andIntroRule,
  }

end VCGen

syntax (name := mvcgen') "mvcgen'"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")?
  (&" simplifying_assumptions" (ppSpace colGt ident)? (" [" ident,* "]")?)?
  (&" with " tactic)? : tactic

/-- Parse grind configuration from the `with grind ...` clause and build `Grind.Params`.
Overrides the internal simp step limit to accommodate large unrolled goals. -/
private meta def elabGrindParams (grindStx : Syntax) (goal : MVarId) : TacticM Grind.Params := do
  let `(tactic| grind $config:optConfig $[only%$only]? $[ [$grindParams:grindParam,*] ]? $[=> $_:grindSeq]?) := grindStx
    | throwUnsupportedSyntax
  let grindConfig ← elabGrindConfig config
  mkGrindParams grindConfig only.isSome (grindParams.getD {}).getElems goal

/--
Build `Sym.Simp.Methods` from a variant name and extra theorems.
Supports the anonymous (default) variant. Named variants require a public
`elabSimpMethods` API in `Lean.Elab.Tactic.Grind.Sym` (see TODO below).
-/
private meta def elabSymSimpParts
    (variantId? : Option (TSyntax `ident))
    (extraIds? : Option (Array (TSyntax `ident)))
    : TacticM Sym.Simp.Methods := do
  let variantName := variantId?.map (·.getId) |>.getD .anonymous
  if !variantName.isAnonymous then
    -- TODO: `resolveExtraTheorems`, `elabVariant`, and `elabSymSimproc` in
    -- `Lean.Elab.Tactic.Grind.Sym` are module-private (non-`public section`).
    -- To support named variants here, we need a public API such as:
    --   `public def elabSymSimp (syn : Syntax) : GrindTacticM (Sym.Simp.Methods × ...)`
    -- exposed from that module, plus a lightweight `GrindTacticM` runner
    -- (the simproc elaborators only use `CoreM`/`MetaM` capabilities).
    throwError "named Sym.simp variants are not yet supported in `mvcgen'`; \
      use `mvcgen' simplifying_assumptions [thm₁, thm₂, ...]` with the default variant instead"
  -- Resolve extra theorems (local hypotheses first, then global constants)
  let mut extraThms : Array Sym.Simp.Theorem := #[]
  if let some ids := extraIds? then
    let lctx ← getLCtx
    for id in ids do
      if let some decl := lctx.findFromUserName? id.getId then
        extraThms := extraThms.push (← Sym.Simp.mkTheoremFromExpr decl.toExpr)
      else
        let declName ← realizeGlobalConstNoOverload id
        extraThms := extraThms.push (← Sym.Simp.mkTheoremFromDecl declName)
  -- Build default variant methods
  let symThms ← Sym.Simp.getSymSimpTheorems
  let pre := Sym.Simp.simpControl >> Sym.Simp.simpArrowTelescope
  let mut post : Sym.Simp.Simproc := Sym.Simp.evalGround >> symThms.rewrite
  if !extraThms.isEmpty then
    let mut thms : Sym.Simp.Theorems := {}
    for thm in extraThms do thms := thms.insert thm
    post := post >> thms.rewrite
  return { pre, post }

private meta def elabSimplifyingAssumptions (simpClause : Syntax) : TacticM (Option Sym.Simp.Methods) := do
  if simpClause.getNumArgs == 0 then return none
  let variantId? := if simpClause[1].getNumArgs != 0 then some ⟨simpClause[1][0]⟩ else none
  let extraIds? := if simpClause[2].getNumArgs != 0
    then some (simpClause[2][1].getSepArgs.map (⟨·⟩)) else none
  pure (some (← elabSymSimpParts variantId? extraIds?))

private meta def elabPreTac (goal : MVarId) (withPreTac : Syntax) : TacticM (VCGen.PreTac × Grind.Params) := do
  let mut params ← Grind.mkDefaultParams {}
  if withPreTac.getNumArgs == 0 then return (.none, params)
  let preTac := withPreTac[1]
  if preTac.getKind == ``Lean.Parser.Tactic.grind then
    params ← elabGrindParams preTac goal
    return (.grind, params)
  else
    return (.tactic preTac, params)

@[tactic mvcgen']
public meta def elabMVCGen' : Tactic := fun stx => withMainContext do
  let goal ← getMainGoal
  let ctx ← VCGen.mkSpecContext stx[1]
  let hypSimpMethods ← elabSimplifyingAssumptions stx[2]
  let (preTac, params) ← elabPreTac goal stx[3]
  let ctx := { ctx with preTac, hypSimpMethods }
  let result ← Grind.GrindM.run (VCGen.main goal ctx) params
  replaceMainGoal (result.invariants ++ result.vcs).toList
