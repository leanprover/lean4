/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.RecursorInfo
import Lean.Meta.SynthInstance
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.FVarSubst

namespace Lean.Meta

private partial def getTargetArity : Expr → Nat
  | Expr.mdata _ b _     => getTargetArity b
  | Expr.forallE _ _ b _ => getTargetArity b + 1
  | e                    => if e.isHeadBetaTarget then getTargetArity e.headBeta else 0

private def addRecParams (mvarId : MVarId) (majorTypeArgs : Array Expr) : List (Option Nat) → Expr → MetaM Expr
  | [], recursor => pure recursor
  | some pos :: rest, recursor =>
    if h : pos < majorTypeArgs.size then
      addRecParams mvarId majorTypeArgs rest (mkApp recursor (majorTypeArgs.get ⟨pos, h⟩))
    else
      throwTacticEx `induction mvarId "ill-formed recursor"
  | none :: rest, recursor => do
    let recursorType ← inferType recursor
    let recursorType ← whnfForall recursorType
    match recursorType with
    | Expr.forallE _ d _ _ => do
      let param ← try synthInstance d catch _ => throwTacticEx `induction mvarId "failed to generate type class instance parameter"
      addRecParams mvarId majorTypeArgs rest (mkApp recursor param)
    | _ =>
      throwTacticEx `induction mvarId "ill-formed recursor"

structure InductionSubgoal where
  mvarId : MVarId
  fields : Array Expr := #[]
  subst  : FVarSubst := {}
  deriving Inhabited

private def getTypeBody (mvarId : MVarId) (type : Expr) (x : Expr) : MetaM Expr := do
  let type ← whnfForall type
  match type with
  | Expr.forallE _ _ b _ => pure $ b.instantiate1 x
  | _                    => throwTacticEx `induction mvarId "ill-formed recursor"

structure AltVarNames where
  explicit : Bool := false   -- true if `@` modifier was used
  varNames : List Name := []
  deriving Inhabited

private partial def finalize
    (mvarId : MVarId) (givenNames : Array AltVarNames) (recursorInfo : RecursorInfo)
    (reverted : Array FVarId) (major : Expr) (indices : Array Expr) (baseSubst : FVarSubst) (recursor : Expr)
    : MetaM (Array InductionSubgoal) := do
  let target ← getMVarType mvarId
  let initialArity := getTargetArity target
  let recursorType ← inferType recursor
  let numMinors := recursorInfo.produceMotive.length
  let rec loop (pos : Nat) (minorIdx : Nat) (recursor recursorType : Expr) (consumedMajor : Bool) (subgoals : Array InductionSubgoal) := do
    let recursorType ← whnfForall recursorType
    if recursorType.isForall && pos < recursorInfo.numArgs then
      if pos == recursorInfo.firstIndexPos then
        let (recursor, recursorType) ← indices.foldlM (init := (recursor, recursorType)) fun (recursor, recursorType) index => do
          let recursor := mkApp recursor index
          let recursorType ← getTypeBody mvarId recursorType index
          pure (recursor, recursorType)
        let recursor := mkApp recursor major
        let recursorType ← getTypeBody mvarId recursorType major
        loop (pos+1+indices.size) minorIdx recursor recursorType true subgoals
      else
        -- consume motive
        let tag ← getMVarTag mvarId
        if minorIdx ≥ numMinors then throwTacticEx `induction mvarId "ill-formed recursor"
        match recursorType with
        | Expr.forallE n d b c =>
          let d := d.headBeta
          -- Remark is givenNames is not empty, then user provided explicit alternatives for each minor premise
          if c.binderInfo.isInstImplicit && givenNames.isEmpty then
            match (← synthInstance? d) with
            | some inst =>
              let recursor := mkApp recursor inst
              let recursorType ← getTypeBody mvarId recursorType inst
              loop (pos+1) (minorIdx+1) recursor recursorType consumedMajor subgoals
            | none => do
              -- Add newSubgoal if type class resolution failed
              let mvar ← mkFreshExprSyntheticOpaqueMVar d (tag ++ n)
              let recursor := mkApp recursor mvar
              let recursorType ← getTypeBody mvarId recursorType mvar
              loop (pos+1) (minorIdx+1) recursor recursorType consumedMajor (subgoals.push { mvarId := mvar.mvarId! })
          else
            let arity := getTargetArity d
            if arity < initialArity then throwTacticEx `induction mvarId "ill-formed recursor"
            let nparams := arity - initialArity -- number of fields due to minor premise
            let nextra  := reverted.size - indices.size - 1 -- extra dependencies that have been reverted
            let minorGivenNames := if h : minorIdx < givenNames.size then givenNames.get ⟨minorIdx, h⟩ else {}
            let mvar ← mkFreshExprSyntheticOpaqueMVar d (tag ++ n)
            let recursor := mkApp recursor mvar
            let recursorType ← getTypeBody mvarId recursorType mvar
            -- Try to clear major premise from new goal
            let mvarId' ← tryClear mvar.mvarId! major.fvarId!
            let (fields, mvarId') ← introN mvarId' nparams minorGivenNames.varNames (useNamesForExplicitOnly := !minorGivenNames.explicit)
            let (extra,  mvarId') ← introNP mvarId' nextra
            let subst := reverted.size.fold (init := baseSubst) fun i (subst : FVarSubst) =>
              if i < indices.size + 1 then subst
              else
                let revertedFVarId := reverted[i]
                let newFVarId      := extra[i - indices.size - 1]
                subst.insert revertedFVarId (mkFVar newFVarId)
            let fields := fields.map mkFVar
            loop (pos+1) (minorIdx+1) recursor recursorType consumedMajor (subgoals.push { mvarId := mvarId', fields := fields, subst := subst })
        | _ => unreachable!
    else
      unless consumedMajor do throwTacticEx `induction mvarId "ill-formed recursor"
      assignExprMVar mvarId recursor
      pure subgoals
  loop (recursorInfo.paramsPos.length + 1) 0 recursor recursorType false #[]

private def throwUnexpectedMajorType {α} (mvarId : MVarId) (majorType : Expr) : MetaM α :=
  throwTacticEx `induction mvarId m!"unexpected major premise type{indentExpr majorType}"

def induction (mvarId : MVarId) (majorFVarId : FVarId) (recursorName : Name) (givenNames : Array AltVarNames := #[]) : MetaM (Array InductionSubgoal) :=
  withMVarContext mvarId do
    trace[Meta.Tactic.induction] "initial\n{MessageData.ofGoal mvarId}"
    checkNotAssigned mvarId `induction
    let majorLocalDecl ← getLocalDecl majorFVarId
    let recursorInfo ← mkRecursorInfo recursorName
    let some majorType ← whnfUntil majorLocalDecl.type recursorInfo.typeName | throwUnexpectedMajorType mvarId majorLocalDecl.type
    majorType.withApp fun _ majorTypeArgs => do
      recursorInfo.paramsPos.forM fun paramPos? => do
        match paramPos? with
        | none          => pure ()
        | some paramPos => if paramPos ≥ majorTypeArgs.size then throwTacticEx `induction mvarId m!"major premise type is ill-formed{indentExpr majorType}"
      let mctx ← getMCtx
      let indices ← recursorInfo.indicesPos.toArray.mapM fun idxPos => do
        if idxPos ≥ majorTypeArgs.size then throwTacticEx `induction mvarId m!"major premise type is ill-formed{indentExpr majorType}"
        let idx := majorTypeArgs.get! idxPos
        unless idx.isFVar do throwTacticEx `induction mvarId m!"major premise type index {idx} is not a variable{indentExpr majorType}"
        majorTypeArgs.size.forM fun i => do
          let arg := majorTypeArgs[i]
          if i != idxPos && arg == idx then
            throwTacticEx `induction mvarId m!"'{idx}' is an index in major premise, but it occurs more than once{indentExpr majorType}"
          if i < idxPos && mctx.exprDependsOn arg idx.fvarId! then
            throwTacticEx `induction mvarId m!"'{idx}' is an index in major premise, but it occurs in previous arguments{indentExpr majorType}"
          -- If arg is also and index and a variable occurring after `idx`, we need to make sure it doesn't depend on `idx`.
          -- Note that if `arg` is not a variable, we will fail anyway when we visit it.
          if i > idxPos && recursorInfo.indicesPos.contains i && arg.isFVar then
            let idxDecl ← getLocalDecl idx.fvarId!
            if mctx.localDeclDependsOn idxDecl arg.fvarId! then
              throwTacticEx `induction mvarId m!"'{idx}' is an index in major premise, but it depends on index occurring at position #{i+1}"
        pure idx
      let target ← getMVarType mvarId
      if !recursorInfo.depElim && mctx.exprDependsOn target majorFVarId then
        throwTacticEx `induction mvarId m!"recursor '{recursorName}' does not support dependent elimination, but conclusion depends on major premise"
      -- Revert indices and major premise preserving variable order
      let (reverted, mvarId) ← revert mvarId ((indices.map Expr.fvarId!).push majorFVarId) true
      -- Re-introduce indices and major
      let (indices', mvarId) ← introNP mvarId indices.size
      let (majorFVarId', mvarId) ← intro1P mvarId
      -- Create FVarSubst with indices
      let baseSubst := do
        let mut subst : FVarSubst := {}
        let mut i := 0
        for index in indices do
          subst := subst.insert index.fvarId! (mkFVar indices'[i])
          i     := i + 1
        pure subst
      trace[Meta.Tactic.induction] "after revert&intro\n{MessageData.ofGoal mvarId}"
      -- Update indices and major
      let indices := indices'.map mkFVar
      let majorFVarId := majorFVarId'
      let major := mkFVar majorFVarId
      withMVarContext mvarId do
        let target ← getMVarType mvarId
        let targetLevel ← getLevel target
        let targetLevel ← normalizeLevel targetLevel
        let majorLocalDecl ← getLocalDecl majorFVarId
        let some majorType ← whnfUntil majorLocalDecl.type recursorInfo.typeName | throwUnexpectedMajorType mvarId majorLocalDecl.type
        majorType.withApp fun majorTypeFn majorTypeArgs => do
          match majorTypeFn with
          | Expr.const majorTypeFnName majorTypeFnLevels _ => do
            let majorTypeFnLevels := majorTypeFnLevels.toArray
            let (recursorLevels, foundTargetLevel) ← recursorInfo.univLevelPos.foldlM (init := (#[], false))
                fun (recursorLevels, foundTargetLevel) (univPos : RecursorUnivLevelPos) => do
                  match univPos with
                  | RecursorUnivLevelPos.motive => pure (recursorLevels.push targetLevel, true)
                  | RecursorUnivLevelPos.majorType idx =>
                    if idx ≥ majorTypeFnLevels.size then throwTacticEx `induction mvarId "ill-formed recursor"
                    pure (recursorLevels.push (majorTypeFnLevels.get! idx), foundTargetLevel)
            if !foundTargetLevel && !targetLevel.isZero then
              throwTacticEx `induction mvarId m!"recursor '{recursorName}' can only eliminate into Prop"
            let recursor := mkConst recursorName recursorLevels.toList
            let recursor ← addRecParams mvarId majorTypeArgs recursorInfo.paramsPos recursor
            -- Compute motive
            let motive := target
            let motive ← if recursorInfo.depElim then mkLambdaFVars #[major] motive else pure motive
            let motive ← mkLambdaFVars indices motive
            let recursor := mkApp recursor motive
            finalize mvarId givenNames recursorInfo reverted major indices baseSubst recursor
          | _ =>
           throwTacticEx `induction mvarId "major premise is not of the form (C ...)"

builtin_initialize registerTraceClass `Meta.Tactic.induction

end Lean.Meta
