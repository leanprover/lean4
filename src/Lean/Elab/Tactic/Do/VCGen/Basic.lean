/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Simp
public import Lean.Elab.Tactic.Do.Attr

public section

namespace Lean.Elab.Tactic.Do

open Lean Parser Elab Tactic Meta Do SpecAttr

builtin_initialize registerTraceClass `Elab.Tactic.Do.vcgen
builtin_initialize registerTraceClass `Elab.Tactic.Do.vcgen.split

register_builtin_option mvcgen.warning : Bool := {
  defValue := true
  descr    := "disable `mvcgen` usage warning"
}

inductive Fuel where
  | limited (n : Nat)
  | unlimited
deriving DecidableEq

declare_config_elab elabConfig VCGen.Config

structure JumpSiteInfo where
  /-- Number of join point arguments. -/
  numJoinParams : Nat
  /-- Index of the match alternative. -/
  altIdx : Nat
  /-- Parameter FVars of the match alternative. -/
  altParams : Array Expr
  /--
  The size of the local context in the alternative after the match has been split and all splitter
  parameters have been introduced.
  This is so that we can construct the `Σ Lᵢ` part of the `hyps` field.
  -/
  altLCtxIdx : Nat
  /--
  MVar to be filled with the stateful hypotheses of the match arm. This should include
  bindings from the local context `Lᵢ` of the call site and is of the form (`x,y,z ∈ Lᵢ`)
  `Σ Lᵢ, ⌜x = a ∧ y = b ∧ z = c⌝ ∧ Hᵢ`, where `..., Lᵢ ⊢ Hᵢ ⊢ₛ wp[jp x y z] Q` is the call site.
  The `Σ Lᵢ` is short for something like
  `let x := ...; ∃ y (h : y = ...), ∃ z, ∃ (h₂ : p)`.
  -/
  hyps : MVarId
  /--
  The proof that jump sites should use to discharge `Hᵢ ⊢ₛ wp[jp a b c] Q`.
  -/
  joinPrf : Expr

structure Context where
  config : VCGen.Config
  specThms : SpecTheorems
  simpCtx : Simp.Context
  simprocs : Simp.SimprocsArray
  jps : FVarIdMap JumpSiteInfo := {}
  initialCtxSize : Nat

structure State where
  fuel : Fuel := .unlimited
  simpState : Simp.State := {}
  /--
  Holes of type `Invariant` or `InvariantNew` that have been generated so far.
  -/
  invariants : Array MVarId := #[]
  /--
  The verification conditions that have been generated so far.
  -/
  vcs : Array MVarId := #[]

abbrev VCGenM := ReaderT Context (StateRefT State MetaM)

def burnOne : VCGenM PUnit := do
  let s ← get
  match s.fuel with
  | Fuel.limited 0 => return ()
  | Fuel.limited (n + 1) => set { s with fuel := .limited n }
  | Fuel.unlimited => return ()

def ifOutOfFuel (x : VCGenM α) (k : VCGenM α) : VCGenM α := do
  let s ← get
  match s.fuel with
  | Fuel.limited 0 => x
  | _ => k

def addSubGoalAsVC (goal : MVarId) : VCGenM PUnit := do
  goal.freshenLCtxUserNamesSinceIdx (← read).initialCtxSize
  let ty ← goal.getType
  if ty.isAppOf ``Std.Do.PostCond || ty.isAppOf ``Std.Do.SPred then
    -- Here we make `mvar` a synthetic opaque goal upon discharge failure.
    -- This is the right call for (previously natural) holes such as loop invariants, which
    -- would otherwise lead to spurious instantiations and unwanted renamings (when leaving the
    -- scope of a local).
    -- But it's wrong for, e.g., schematic variables. The latter should never be PostConds,
    -- Invariants or SPreds, hence the condition.
    goal.setKind .syntheticOpaque
  if ty.isAppOf ``Std.Do.Invariant || ty.isAppOf ``Std.Do.InvariantNew then
    modify fun s => { s with invariants := s.invariants.push goal }
  else
    modify fun s => { s with vcs := s.vcs.push goal }

def emitVC (subGoal : Expr) (name : Name) : VCGenM Expr := do
  let m ← liftM <| mkFreshExprSyntheticOpaqueMVar subGoal (tag := name)
  addSubGoalAsVC m.mvarId!
  return m

def liftSimpM (x : SimpM α) : VCGenM α := do
  let ctx ← read
  let s ← get
  let mref := (Simp.mkDefaultMethodsCore ctx.simprocs).toMethodsRef
  let (a, simpState) ← x mref ctx.simpCtx |>.run s.simpState
  set { s with simpState }
  return a

instance : MonadLift SimpM VCGenM where
  monadLift x := liftSimpM x

def withJP (jp : FVarId) (info : JumpSiteInfo) : VCGenM α → VCGenM α :=
  ReaderT.adapt fun ctx => { ctx with jps := ctx.jps.insert jp info }

def knownJP? (jp : FVarId) : VCGenM (Option JumpSiteInfo) := do
  return (← read).jps.get? jp

def isDuplicable (e : Expr) : Bool := match e with
  | .bvar .. => true
  | .mvar .. => true
  | .fvar .. => true
  | .const .. => true
  | .lit .. => true
  | .sort .. => true
  | .mdata _ e => isDuplicable e
  | .proj _ _ e => isDuplicable e
  | .lam .. => false
  | .forallE .. => false
  | .letE .. => false
  | .app .. => e.isAppOf ``OfNat.ofNat

def withLetDeclShared (name : Name) (type : Expr) (val : Expr) (k : Bool → Expr → (Expr → VCGenM Expr) → VCGenM α) (kind : LocalDeclKind := .default) : VCGenM α :=
  if isDuplicable val then
    k false val pure
  else
    withLetDecl name type val (kind := kind) fun fv => do
      k true fv (liftM <| mkLetFVars #[fv] ·)

/-- TODO: Fix this when rewriting the do elaborator -/
def isJP (n : Name) : Bool := n.eraseMacroScopes == `__do_jp

partial def getNumJoinParams (joinTy : Expr) (resTy : Expr) : MetaM Nat := do
  if joinTy.isMData then
    return ← getNumJoinParams joinTy.consumeMData resTy
  if joinTy == resTy then
    return 0
  else if joinTy.isForall then
    return 1 + (← getNumJoinParams joinTy.consumeMData.bindingBody! resTy)
  else
    throwError "getNumJoinParams: residual joinTy not a forall: {joinTy}"

/-- Reduces (1) Prod projection functions and (2) Projs in application heads,
and (3) beta reduces. Will not unfold projection functions unless further beta reduction happens. -/
partial def reduceProjBeta? (e : Expr) : MetaM (Option Expr) :=
  go none e.getAppFn e.getAppRevArgs
  where
    go lastReduction f rargs := do
      match f with
      | .mdata _ f => go lastReduction f rargs
      | .app f a => go lastReduction f (rargs.push a)
      | .lam .. =>
        if rargs.size = 0 then return lastReduction
        let e' := f.betaRev rargs
        go (some e') e'.getAppFn e'.getAppRevArgs
      | .const name .. =>
        let env ← getEnv
        match env.getProjectionStructureName? name with
        | some ``Prod => -- only reduce fst and snd for now
          match ← Meta.unfoldDefinition? (mkAppRev f rargs) with
          | some e' => go lastReduction e'.getAppFn e'.getAppRevArgs
          | none => pure lastReduction
        | _ => pure lastReduction
      | .proj .. => match ← reduceProj? f with
        | some f' =>
          let e' := mkAppRev f' rargs
          go (some e') e'.getAppFn e'.getAppRevArgs
        | none    => pure lastReduction
      | .letE x ty val body nondep =>
        match ← go none body rargs with
        | none => pure lastReduction
        | some body' => pure (some (.letE x ty val body' nondep))
      | _ => pure lastReduction

def mkSpecContext (optConfig : Syntax) (lemmas : Syntax) (ignoreStarArg := false) : TacticM Context := do
  let config ← elabConfig optConfig
  let mut specThms ← getSpecTheorems
  let mut simpStuff := #[]
  let mut starArg := false
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``simpErase then
      try
        -- Try and build SpecTheorems for the lemma to erase to see if it's
        -- meant to be interpreted by SpecTheorems. Otherwise fall back to SimpTheorems.
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
        let info ← getConstInfo declName
        try
          let thm ← mkSpecTheoremFromConst declName
          specThms := specThms.add thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | some (.fvar fvar) =>
        let decl ← getFVarLocalDecl (.fvar fvar)
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := specThms.add thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | _ => withRef term <| throwError "Could not resolve {repr term}"
    else if arg.getKind == ``simpStar then
      starArg := true
      simpStuff := simpStuff.push ⟨arg⟩
    else
      throwUnsupportedSyntax
  -- Build a mock simp call to build a simp context that corresponds to `simp [simpStuff]`
  let stx ← `(tactic| simp +unfoldPartialApp -zeta [$(Syntax.TSepArray.ofElems simpStuff),*])
  -- logInfo s!"{stx}"
  let res ← mkSimpContext stx.raw
    (eraseLocal := false)
    (simpTheorems := getSpecSimpTheorems)
    (ignoreStarArg := ignoreStarArg)
  -- logInfo m!"{res.ctx.simpTheorems.map (·.toUnfold.toList)}"
  if starArg && !ignoreStarArg then
    let fvars ← getPropHyps
    for fvar in fvars do
      unless specThms.isErased (.local fvar) do
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := specThms.add thm
        catch _ => continue
  return {
    config,
    specThms,
    simpCtx := res.ctx,
    simprocs := res.simprocs
    initialCtxSize := (← getLCtx).numIndices
  }

def withLocalSpecs [Monad m] [MonadControlT VCGenM m] (xs : Array Expr) (k : m α) : m α :=
  controlAt VCGenM fun runInBase => do
    let rec loop i : VCGenM _ := do
      if h : i < xs.size then
        let x := xs[i]
        try
          let thm ← mkSpecTheoremFromLocal x.fvarId! (eval_prio low)
          trace[Elab.Tactic.Do.vcgen] "adding {thm.proof}"
          withReader (fun ctx => { ctx with specThms := ctx.specThms.add thm }) (loop (i + 1))
        catch ex =>
          match ex with
          | .internal .. => throw ex
          | .error ..    => loop (i + 1)
      else
        runInBase k
    loop 0
