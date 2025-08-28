/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian, Robin Arnez
-/
module

prelude
public import Lean.Meta.Constructions.CasesOn
public import Lean.Meta.Match.Match
public import Lean.Meta.Tactic.SolveByElim

public section

namespace Lean.Meta.IndPredBelow

structure Context where
  /-- The names of level parameters -/
  levelParams : List Name
  /-- Inductive eliminates into any universe -/
  largeElim : Bool
  /-- Parameters of the mutual inductive -/
  params : Array Expr
  /-- The motives (fvars) -/
  motives : Array Expr
  /-- Map from motive to motive index (opposite of `motives[·]`) -/
  motiveToIdx : FVarIdMap Nat
  /-- The minor premises (fvars) -/
  minors : Array Expr
  /-- Recursor names (corresponding to the motives) -/
  recNames : Array Name
  /-- Names of below declarations (corresponding to the motives) -/
  belowNames : Array Name
  /-- Names of brecOn declarations (corresponding to the motives) -/
  brecOnNames : Array Name

/-- Is `type` a motive nested in foralls and applications? -/
def isIH (type : Expr) (ctx : Context) : MetaM (Option Nat) := do
  let .fvar f := type.getForallBody.getAppFn | return none
  return ctx.motiveToIdx.get? f

/-- Returns `@XYZ.below params... motives...` -/
def mkBelowAppOfIdx (i : Nat) (ctx : Context) : Expr :=
  let const := .const (ctx.belowNames[i]!) (ctx.levelParams.map Level.param)
  mkAppN (mkAppN const ctx.params) ctx.motives

/--
Replaces the application of the motive with the corresponding below name.
Example:
```
(a : Nat) → motive (f a)
==>
(a : Nat) → ABC.below (f a)
```
-/
def ihTypeToBelowType : Expr → Context → Expr
  | .fvar f, ctx => mkBelowAppOfIdx (ctx.motiveToIdx.get! f) ctx
  | .app f a, ctx => .app (ihTypeToBelowType f ctx) a
  | .forallE nm t b bi, ctx => .forallE nm t (ihTypeToBelowType b ctx) bi
  | _, _=> unreachable!

def toImplicit (e : Expr) : Expr :=
  match e with
  | .forallE _ t b@(.forallE ..) _ => e.updateForall! .implicit t (toImplicit b)
  | e => e

/-- Generate `belowNames[motiveIdx]` -/
def mkBelowInductive (motiveIdx minorIdx : Nat) (ctx : Context) : MetaM (Nat × InductiveType) := do
  let motive := ctx.motives[motiveIdx]!
  let motiveType ← inferType motive
  let name := ctx.belowNames[motiveIdx]!
  let paramsAndMotives := ctx.params ++ ctx.motives
  let type ← mkForallFVars paramsAndMotives (toImplicit motiveType)
  let mut minorIdx := minorIdx
  let mut ctors := #[]
  -- iterate through all minors with motive `motive`
  while minorIdx < ctx.minors.size do
    let minor := ctx.minors[minorIdx]!
    let minorName ← minor.fvarId!.getUserName
    let minorType ← inferType minor
    if minorType.getForallBody.getAppFn != motive then
      break
    let ctorName := name ++ minorName
    let ctorType ← forallTelescope minorType fun minorArgs body => do
      let rec go (i : Nat) (vars : Array Expr) : MetaM Expr := do
        if h : i < minorArgs.size then
          let type ← inferType minorArgs[i]
          if let some _ ← isIH type ctx then
            -- minorArgs[i] : (a : Nat) → motive (f a)
            -- ==> (ih : (a : Nat) → ABC.below (f a)) (ih_1 : (a : Nat) → motive (f a))
            withLocalDeclD (← mkFreshUserName `ih) (ihTypeToBelowType type ctx) fun below =>
              go (i + 1) ((vars.push below).push minorArgs[i])
          else
            go (i + 1) (vars.push minorArgs[i])
        else
          mkForallFVars vars (ihTypeToBelowType body ctx)
      termination_by minorArgs.size - i
      go 0 paramsAndMotives
    ctors := ctors.push {
      name := ctorName
      type := ctorType
    }
    minorIdx := minorIdx + 1
  let induct : InductiveType := { name, type, ctors := ctors.toList }
  return (minorIdx, induct)

def mkBelowInductives (ctx : Context) : MetaM Unit := do
  let nmotives := ctx.motives.size
  let mut minorIdx := 0
  let mut inducts := #[]
  for i in *...nmotives do
    let (newIdx, ind) ← mkBelowInductive i minorIdx ctx
    inducts := inducts.push ind
    minorIdx := newIdx
  let nparams := ctx.params.size + ctx.motives.size
  Lean.addDecl <| .inductDecl ctx.levelParams nparams inducts.toList false
  for b in ctx.belowNames do
    Lean.mkCasesOn b

def withBRecOnArgs (k : (newMinors : Array Expr) → (proofArgs : Array Expr) → MetaM Unit) (ctx : Context) : MetaM Unit := do
  let rec go (i : Nat) (newMinors : Array Expr) : MetaM Unit := do
    if h : i < ctx.motives.size then
      let motive := ctx.motives[i]
      let motiveType ← inferType motive
      -- {motive : (a : Nat) → (x : ABC a) → Prop}
      -- ==> (F_1 : (a : Nat) → (x : ABC a) → ABC.below x → motive a x)
      let type ← forallTelescope motiveType fun majors _ => do
        let type ← mkArrow (mkAppN (mkBelowAppOfIdx i ctx) majors) (mkAppN motive majors)
        mkForallFVars majors type
      withLocalDeclD ((`F).appendIndexAfter (i + 1)) type fun minor =>
        go (i + 1) (newMinors.push minor)
    else
      -- #[@ABC.below params... motives..., ...]
      let recMotives := (Array.range ctx.motives.size).map (mkBelowAppOfIdx · ctx)
      let mut recMinors := #[]
      for minor in ctx.minors do
        let minorType ← inferType minor
        let i := ctx.motiveToIdx.get! minorType.getForallBody.getAppFn.fvarId!
        let name ← minor.fvarId!.getUserName
        let belowCtorName := ctx.belowNames[i]! ++ name
        let expr ← forallTelescope minorType fun minorArgs res => do
          let rec go2 (j : Nat) (vars args : Array Expr) : MetaM Expr := do
            if h : j < minorArgs.size then
              let type ← inferType minorArgs[j]
              if let some i' ← isIH type ctx then
                -- minorArgs[j] : (a : Nat) → motive (f a)
                -- newIH : (a : Nat) → ABC.below (f a)
                withLocalDeclD (← mkFreshUserName `ih) (ihTypeToBelowType type ctx) fun newIH => do
                  -- proof = (fun a => F_1 (f a) (newIH a))
                  let proof ← forallTelescope type fun args body => do
                    let proof := .app (body.updateFn newMinors[i']!) (mkAppN newIH args)
                    mkLambdaFVars args proof
                  -- fun ... ih => ... ih (fun a => F_1 (f a) (newIH a))
                  go2 (j + 1) (vars.push newIH) ((args.push newIH).push proof)
              else
                go2 (j + 1) (vars.push minorArgs[j]) (args.push minorArgs[j])
            else
              -- constructor ABC.test (f : Nat → Nat) (h : (a : Nat) → ABC (f a)) : ABC (f 0 + f 1)
              -- proof = (fun f h ih => @ABC.below.test motive f h ih (fun a => F_1 (f a) (ih a)))
              let belowCtor := .const belowCtorName (ctx.levelParams.map Level.param)
              let proof := mkAppN (mkAppN (mkAppN belowCtor ctx.params) ctx.motives) args
              mkLambdaFVars vars proof
          termination_by minorArgs.size - j
          go2 0 #[] #[]
        recMinors := recMinors.push expr
      k newMinors (ctx.params ++ recMotives ++ recMinors)
  termination_by ctx.motives.size - i
  go 0 #[]

def mkBRecOn (ctx : Context) : MetaM Unit := do
  withBRecOnArgs (ctx := ctx) fun newMinors proofArgs => do
    let nmotives := ctx.motives.size
    let lparams := ctx.levelParams.map Level.param
    let lparams := if ctx.largeElim then levelZero :: lparams else lparams
    for i in *...nmotives do
      let motive := ctx.motives[i]!
      let motiveType ← inferType motive
      forallTelescope motiveType fun majors _ => do
        let lctx := majors.foldl (fun lctx var => lctx.setBinderInfo var.fvarId! .implicit)
          (← getLCtx) 0 (majors.size - 1)
        withLCtx' lctx do
          let recApp := mkAppN (mkAppN (.const ctx.recNames[i]! lparams) proofArgs) majors
          let proof := .app (mkAppN newMinors[i]! majors) recApp
          let type := mkAppN motive majors
          let vars := ctx.params ++ ctx.motives ++ majors ++ newMinors
          let proof ← mkLambdaFVars vars proof
          let type ← mkForallFVars vars type
          addDecl <| .thmDecl {
            name := ctx.brecOnNames[i]!
            levelParams := ctx.levelParams
            type := type
            value := proof
          }

/--
Do we match on an expression that corresponds to a `below` proof?
If so, return the proof and its type.
-/
def detectRecPredApp (x : Expr) : MetaM (Option (Expr × Name)) := do
  let x ← whnfCore x
  x.withApp fun fn args => do
    unless fn.isFVar do
      return none
    let env ← getEnv
    return (← getLCtx).findDecl? fun decl =>
      let rec go (argIdx : Nat) (e : Expr) := do
        if h : argIdx < args.size then
          match e with
          | .forallE _ _ b _ => go (argIdx + 1) (b.instantiate1 args[argIdx])
          | _ => none
        else
          let .app f a := e.getForallBody | none
          unless a.getAppFn == fn do none
          let .const belowName@(.str n s) _ := f.getAppFn | none
          unless s = "below" ∨ (s.dropPrefix? "below_").any (·.isNat) do none
          unless (env.findAsync? n).any (·.kind == .induct) do none
          some (mkAppN decl.toExpr args, belowName)
      termination_by args.size - argIdx
      go 0 decl.type

/--
Given `val` which corresponds to a constructor of a below inductive,
and `paramCount` which is the number of parameters in the real inductive,
return the indices of the fields corresponding to recursive calls.
-/
def belowRecIndices (val : ConstructorVal) (paramCount : Nat) : MetaM (Array Nat) := do
  forallTelescope val.type fun vars _ => do
    let motives := vars.extract paramCount val.numParams
    vars.filterMapM (start := val.numParams) fun e => do
      let type ← inferType e
      let .app f a := type.getForallBody | return none
      let a@(.fvar _) := a.getAppFn | return none
      let f@(.fvar _) := f.getAppFn | return none
      unless motives.contains f do return none
      return vars.idxOf a - val.numParams

open Match

/--
This function adds an additional `below` discriminant to a matcher application.
It is used for modifying the patterns, such that the structural recursion can use the new
`below` predicate instead of the original one and thus be used prove structural recursion.
`belowParams` are the parameters for the `below` applications where the first `nrealParams` are
actual parameters and the remaining are motives.
-/
partial def mkBelowMatcher (matcherApp : MatcherApp) (belowParams : Array Expr) (nrealParams : Nat) :
    MetaM (Option (Expr × MetaM Unit)) :=
  withTraceNode `Meta.IndPredBelow (return m!"{exceptEmoji ·} {matcherApp.toExpr} and {belowParams}") do
  let mut input ← getMkMatcherInputInContext matcherApp
  let mut discrs := matcherApp.discrs
  let mut matchTypeAdd := #[] -- #[(discrIdx, ), ...]
  let mut i := discrs.size
  let oldVarCounts := input.lhss.toArray.map (·.fvarDecls.length)
  while i > 0 do
    i := i - 1
    let discr := discrs[i]!
    if let some (below, belowName) ← detectRecPredApp discr then
      let val ← getConstInfoInduct belowName
      discrs := discrs.insertIdx! (i + 1) below
      -- | a, b, ABC.thing ..., c, d ==> | a, b, .(ABC.thing ...), ABC.below.thing ..., c, d
      let lhss ← input.lhss.mapM (addBelowPattern belowName i)
      input := { input with discrInfos := input.discrInfos.insertIdx! (i + 1) {}, lhss }
      matchTypeAdd := matchTypeAdd.push (i, belowName)
  if matchTypeAdd.isEmpty then
    return none
  -- adds below vars in between the existing vars
  let rec addVars (j : Nat) (vars : Array Expr) (k : Array Expr → MetaM Expr) : MetaM Expr := do
    if h : j < matchTypeAdd.size then
      let (i, belowIndName) := matchTypeAdd[j]
      let type ← toBelowType belowIndName vars[i]!
      withLocalDeclD `below type fun var => addVars (j + 1) (vars.insertIdx! (i + 1) var) k
    else
      k vars
  -- adjust match type by inserting `ABC.below ...`
  input ← forallTelescope input.matchType fun vars body => do
    let matchType ← addVars 0 vars (mkForallFVars · body)
    return { input with matchType }
  -- adjust motive by inserting `ABC.below ...`
  let motive ← lambdaTelescope matcherApp.motive fun vars body =>
    addVars 0 vars (mkLambdaFVars · body)

  let matcherName ← mkFreshUserName input.matcherName
  let res ← Match.mkMatcher { input with matcherName }
  res.addMatcher
  -- if a wrong index is picked, the resulting matcher can be type-incorrect (really?).
  -- we check here, so that errors can propagate higher up the call stack.
  check res.matcher

  let hasEqns := input.discrInfos.any (·.hName?.isSome)
  let alts ← matcherApp.alts |>.mapIdxM fun idx alt => do
    let lhs := input.lhss[idx]!
    let oldCount := oldVarCounts[idx]!
    -- we add new fvars to the end so all `oldCount` previous ones are preserved
    withExistingLocalDecls lhs.fvarDecls do
    lambdaBoundedTelescope alt oldCount fun oldAltVars t => do
      let fvars := lhs.fvarDecls.toArray.map (·.toExpr)
      let t :=
        -- special case: previously `Unit → motive ...`, now has variables
        match oldCount, hasEqns, fvars.size with
        | 0, false, _ + 1 => t.bindingBody!
        | _, _, _ => t
      let oldVars := fvars.extract 0 oldCount
      let t := t.replaceFVars oldAltVars oldVars
      trace[Meta.IndPredBelow.match] "oldAltVars = {oldAltVars}; oldCount = {oldCount}; fvars = {fvars}"
      let newAlt ← mkLambdaFVars fvars t
      trace[Meta.IndPredBelow.match] "alt {idx}:\n{alt} ↦ {newAlt}"
      pure newAlt

  let newApp := mkApp res.matcher motive
  let newApp := mkAppN newApp discrs
  let newApp := mkAppN newApp alts
  return some (newApp, res.addMatcher)

where
  addBelowPattern (indName : Name) (idx : Nat) (lhs : AltLHS) : MetaM AltLHS := do
    withExistingLocalDecls lhs.fvarDecls do
    let prevPatterns := lhs.patterns.take idx
    let (originalPattern :: morePatterns) := lhs.patterns.drop idx |
      throwError "invalid amount of patterns"
    let ((predPattern, belowPattern), fVars) ← (convertToBelow indName originalPattern none).run #[]
    withExistingLocalDecls fVars.toList do
    let patterns := prevPatterns ++ predPattern :: belowPattern :: morePatterns
    return { lhs with patterns, fvarDecls := lhs.fvarDecls ++ fVars.toList }

  /--
  `ABC.below`, `h : ∀ x y z, ABC a b c` ===>
  `∀ x y z, @ABC.below params... motives... a b c (h x y z)`
  -/
  toBelowType (belowIndName : Name) (h : Expr) : MetaM Expr := do
    let type ← inferType h
    forallTelescopeReducing (whnfType := true) type fun moreVars body => do
      body.withApp fun f args => do
        let .const nm us := f | throwError "expected constant application at {type}"
        let ind ← getConstInfoInduct nm
        let tgtType := mkAppN (.const belowIndName us) belowParams
        let tgtType := mkAppN tgtType (args.extract ind.numParams)
        let tgtType := .app tgtType (mkAppN h moreVars)
        mkForallFVars moreVars tgtType

  /--
  Converts a pattern that matches on `h : ∀ x y z..., ABC ...` (where `ABC` is an inductive
  predicate) into two patterns: One that still matches on the same type as before and
  another that matches on `∀ x y z..., belowIndName ... (h x y z)`. This function assumes that
  `belowIndName` corresponds to a `below` inductive for `ABC` (for nested inductive predicates this
  may not be `ABC.below`).
  The goal of this function is to get as many motive proofs (used for recursive applications) and
  below proofs (used for further matches) as possible. In the default case, it will simply keep the
  original pattern and introduce a new variable of type `∀ x y z..., belowIndName ... (h x y z)` as
  the below pattern.
  -/
  convertToBelow (belowIndName : Name) (originalPattern : Pattern) (var? : Option Expr) :
      StateRefT (Array LocalDecl) MetaM (Pattern × Pattern) := do
    match originalPattern with
    | .ctor ctorName us params fields =>
      withTraceNode `Meta.IndPredBelow.match (return m!"{exceptEmoji ·} pattern {← originalPattern.toExpr} to {belowIndName}") do
      let ctorInfo ← getConstInfoCtor ctorName
      let shortCtorName := ctorName.replacePrefix ctorInfo.induct .anonymous
      let belowCtor ← getConstInfoCtor (belowIndName ++ shortCtorName)
      let type := belowCtor.instantiateTypeLevelParams us
      let fieldExprs ← fields.toArray.mapM (·.toExpr)
      trace[Meta.IndPredBelow.match] "instantiate {type} with {belowParams} {fieldExprs}}"
      let type ← instantiateForall type belowParams
      let type ← instantiateForall type fieldExprs
      let recIdxs ← belowRecIndices belowCtor nrealParams
      trace[Meta.IndPredBelow.match] "rec indices {.ofConstName belowCtor.name} {recIdxs}"
      forallTelescope type fun vars _ => do
        -- even var indices are `below`s, odd indices `motive`s
        let mut belowFields := fields.toArray
        let mut i := 0
        let mut curDeclCount := (← get).size
        while h : i < vars.size do
          let var := vars[i]
          let varType ← inferType var
          let belowArg := varType.getForallBody.appArg!
          let belowInd := varType.getForallBody.getAppFn.constName!
          let realIdx := recIdxs[i / 2]!
          trace[Meta.IndPredBelow.match] "transform {var} to {realIdx}, {belowFields[realIdx]!.toMessageData}"
          let (predPattern, belowPattern) ← convertToBelow belowInd belowFields[realIdx]! var
          belowFields := belowFields.set! realIdx predPattern
          -- add motive decl var
          let localDecl ← getFVarLocalDecl vars[i + 1]!
          modify fun decls => decls.push localDecl
          belowFields := belowFields.push belowPattern
          belowFields := belowFields.push (.var vars[i + 1]!.fvarId!)
          i := i + 2
        let ctor := .ctor belowCtor.name us belowParams.toList belowFields.toList
        if ← isTracingEnabledFor `Meta.IndPredBelow.match then
          withExistingLocalDecls ((← get).extract curDeclCount).toList do
            trace[Meta.IndPredBelow.match] "{originalPattern.toMessageData} ↦ {ctor.toMessageData}"
        --let ctorExpr := mkAppN (mkAppN (mkConst ctorName us) params.toArray) fieldExprs
        let ctorExpr ← originalPattern.toExpr
        return (.inaccessible ctorExpr, ctor)
    | .as varId p hId =>
      let (predPattern, belowPattern) ← convertToBelow belowIndName p var?
      return (.as varId predPattern hId, belowPattern)
    | _ =>
      -- variables, inaccessibles ==> we can't
      let oldH ← originalPattern.toExpr
      if let some var := var? then
        let localDecl ← getFVarLocalDecl var
        modify fun decls => decls.push localDecl
        return (originalPattern, .var var.fvarId!)
      let tgtType ← toBelowType belowIndName oldH
      withLocalDeclD (← mkFreshUserName `h) tgtType fun newH => do
        let localDecl ← getFVarLocalDecl newH
        modify fun decls => decls.push localDecl
        return (originalPattern, .var newH.fvarId!)

/-- Generates the auxiliary lemmas `below` and `brecOn` for a recursive inductive predicate. -/
def mkBelow (indName : Name) : MetaM Unit :=
  withTraceNode `Meta.IndPredBelow (fun _ => return m!"{indName}") do
  unless (← isInductivePredicate indName) do return
  let indVal ← getConstInfoInduct indName
  if indVal.isUnsafe || !indVal.isRec then return
  let levelParams := indVal.levelParams
  let recVal ← getConstInfoRec (indName ++ `rec)
  let largeElim := recVal.levelParams.length > levelParams.length
  let t := if largeElim then recVal.instantiateTypeLevelParams [.zero] else recVal.type
  let n := recVal.numParams + recVal.numMotives + recVal.numMinors
  forallBoundedTelescope t (some n) fun as _ => do
    let params := as.extract 0 recVal.numParams
    let motives := as.extract recVal.numParams (recVal.numParams + recVal.numMotives)
    let minors := as.extract (recVal.numParams + recVal.numMotives)
    let motiveToIdx := motives.zipIdx.foldl (init := ∅) fun a (e, n) => a.insert e.fvarId! n
    let recNames := indVal.all.toArray.map (· ++ `rec) ++
      (Array.range' 1 indVal.numNested).map (indVal.all.head! ++ `rec).appendIndexAfter
    let belowNames := indVal.all.toArray.map (· ++ `below) ++
      (Array.range' 1 indVal.numNested).map (indVal.all.head! ++ `below).appendIndexAfter
    let brecOnNames := indVal.all.toArray.map (· ++ `brecOn) ++
      (Array.range' 1 indVal.numNested).map (indVal.all.head! ++ `brecOn).appendIndexAfter
    let ctx := { levelParams, largeElim, params, motives, motiveToIdx, minors, recNames, belowNames, brecOnNames }
    mkBelowInductives ctx
    mkBRecOn ctx

builtin_initialize
  registerTraceClass `Meta.IndPredBelow
  registerTraceClass `Meta.IndPredBelow.match

end Lean.Meta.IndPredBelow
