/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian, Robin Arnez
-/
module

prelude
public import Lean.Meta.Match.MatcherApp.Basic
import Lean.Meta.Constructions.CasesOn
import Lean.Meta.Match.Match
import Init.Data.Nat.Linear
import Init.Omega

/-!
# The `below` and `brecOn` constructions for inductive predicates

This module defines the `below` and `brecOn` constructions for inductive predicates.
While the `brecOn` construction for inductive predicates is structurally identical to the one for
regular types apart from only eliminating to propositions, the `below` construction is changed
since it is unlike for types not possible to eliminate proofs of inductive predicates to `Prop`s
containing nested proofs. Instead, each `below` declaration is defined as an inductive type with one
constructor per constructor of the original inductive, containing additional motive proofs and
nested below proofs.

Additionally, this module defines the function `mkBelowMatcher` which can be used to rewrite match
expressions to expose these motive proofs and nested below proofs.
-/

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
def isIH (type : Expr) (ctx : Context) : Option Nat := do
  let .fvar f := type.getForallBody.getAppFn | none
  ctx.motiveToIdx.get? f

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
          if let some _ := isIH type ctx then
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
              if let some i' := isIH type ctx then
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

/-- Generates the auxiliary lemmas `below` and `brecOn` for a recursive inductive predicate. -/
public def mkBelow (indName : Name) : MetaM Unit :=
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

/--
Given `val` which corresponds to a constructor of a below inductive,
and `paramCount` which is the number of parameters in the real inductive,
return the indices of the fields corresponding to recursive calls.
-/
def belowRecIndices (val : ConstructorVal) (paramCount : Nat) : MetaM (Array (Nat × Nat)) := do
  forallTelescope val.type fun vars _ => do
    let motives := vars.extract paramCount val.numParams
    vars.filterMapM (start := val.numParams) fun e => do
      let type ← inferType e
      let .app f a := type.getForallBody | return none
      let a@(.fvar _) := a.getAppFn | return none
      let f@(.fvar _) := f.getAppFn | return none
      let some motiveIdx := motives.idxOf? f | return none
      return (motiveIdx, vars.idxOf a - val.numParams)

open Match

/--
Records below proofs and motive proofs available. This is extended using `NewDecl`s while visiting
and rewriting match expressions.
-/
public structure RecursionContext where
  /--
  Map from proofs `h : ∀ x y z, ...` to pairs of `belowIndName` and a proof of
  `h' : ∀ x y z, belowIndName ... (h x y z)`. These are used to find match rewriting candidates.
  -/
  belows : FVarIdMap (Name × Expr)
  /--
  Map from proofs `h : ∀ x y z, ...` to pairs of `n` and a proof of
  `h' : ∀ x y z, <nth motive> ... (h' x y z)` (nth motive corresponds to the order of motives in
  the recursor). These are used to eliminate recursive calls.
  -/
  motives : FVarIdMap (Nat × Expr)

instance : ToMessageData RecursionContext where
  toMessageData ctx :=
    "\nBelows:\n" ++
    toMessageData (ctx.belows.toArray.map (fun (var, nm, e) => (Expr.fvar var, nm, e)))
    ++ "\nMotives:\n" ++
    toMessageData (ctx.motives.toArray.map (fun (var, nm, e) => (Expr.fvar var, nm, e)))

/--
New local declarations that were added in the process of adding below discriminants to a matcher
with information on their purpose.
-/
inductive NewDecl where
  /-- A new declaration of type `∀ x y z, indName ... (h x y z)` for all `h ∈ vars` -/
  | below (decl : LocalDecl) (indName : Name) (vars : Array FVarId)
  /-- A new declaration of type `∀ x y z, <nth motive> ... (h x y z)` for all `h ∈ vars` -/
  | motive (decl : LocalDecl) (motiveIdx : Nat) (vars : Array FVarId)

instance : ToMessageData NewDecl where
  toMessageData
  | .below decl indName vars =>
    m!"Below: {decl.toExpr}, {indName}, {vars.map Expr.fvar}"
  | .motive decl idx vars =>
    m!"Motive: {decl.toExpr}, {idx}, {vars.map Expr.fvar}"

def NewDecl.getDecl : NewDecl → LocalDecl
  | .below decl _ _ => decl
  | .motive decl _ _ => decl

/--
Given a pattern `p`, return an array of variables that bind `p` completely (i.e. variables and
named patterns).
-/
def collectDirectVarsInPattern (p : Pattern) : Array FVarId :=
  go p #[]
where
  go (p : Pattern) (a : Array FVarId) : Array FVarId :=
    match p with
    | .var v => a.push v
    | .as v p' _ => go p' (a.push v)
    | _ => a

/--
This function adds an additional `below` discriminant to a matcher application and transforms each
alternative with the provided `transformAlt` function. The provided recursion context is used for
finding below proofs that correspond to discriminants and is extended with new proofs when calling
`transformAlt`. `belowParams` should contain parameters and motives for `below` applications where
the first `nrealParams` are parameters and the remaining are motives.
-/
public partial def mkBelowMatcher (matcherApp : MatcherApp) (belowParams : Array Expr) (nrealParams : Nat)
    (ctx : RecursionContext) (transformAlt : RecursionContext → Expr → MetaM Expr) :
    MetaM (Option (Expr × MetaM Unit)) :=
  withTraceNode `Meta.IndPredBelow.match (return m!"{exceptEmoji ·} {matcherApp.toExpr} and {belowParams}") do
  let mut input ← getMkMatcherInputInContext matcherApp (unfoldNamed := false)
  let mut discrs := matcherApp.discrs
  let mut matchTypeAdd := #[] -- #[(discrIdx, ), ...]
  let mut i := discrs.size
  let oldVarCounts := input.lhss.toArray.map (·.fvarDecls.length)
  let mut newDecls := Array.replicate oldVarCounts.size #[]
  while i > 0 do
    i := i - 1
    let discr := discrs[i]!
    let discr ← whnfCore discr
    let .fvar var := discr.getAppFn | continue
    let some (belowName, below) := ctx.belows.get? var | continue
    let val ← getConstInfoInduct belowName
    discrs := discrs.insertIdx! (i + 1) (mkAppN below discr.getAppArgs)
    -- | a, b, ABC.thing ..., c, d ==> | a, b, .(ABC.thing ...), ABC.below.thing ..., c, d
    let mut newLHSs := #[]
    let mut lhssArray := input.lhss.toArray
    for h : j in *...lhssArray.size do
      let (newLHS, newDeclsAdd) ← addBelowPattern belowName i lhssArray[j]
      newLHSs := newLHSs.push newLHS
      newDecls := newDecls.modify j (· ++ newDeclsAdd)
    input := { input with discrInfos := input.discrInfos.insertIdx! (i + 1) {}, lhss := newLHSs.toList }
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

  let matcherName ← mkAuxDeclName `match
  let res ← Match.mkMatcher { input with matcherName }
  res.addMatcher
  -- if a wrong index is picked, the resulting matcher can be type-incorrect (really?).
  -- we check here, so that errors can propagate higher up the call stack.
  check res.matcher

  let hasEqns := input.discrInfos.any (·.hName?.isSome)
  let alts ← matcherApp.alts |>.mapIdxM fun idx alt => do
    let lhs := input.lhss[idx]!
    let oldCount := oldVarCounts[idx]!
    let newDecls := newDecls[idx]!
    -- we add new fvars to the end so all `oldCount` previous ones are preserved
    -- Note: these free variables are guaranteed to be unique because they are created in
    -- `getMkMatcherInputInContext` and/or `convertToBelow`.
    withExistingLocalDecls lhs.fvarDecls do
      trace[Meta.IndPredBelow.match] "new decls:\n{newDecls}"
      let fvars := lhs.fvarDecls.toArray.map (·.toExpr)
      let oldVars := fvars.extract 0 oldCount
      let t := alt.beta oldVars
      let t :=
        -- special case: previously `Unit → motive ...`, now has variables
        match oldCount, hasEqns, fvars.size with
        | 0, false, _ + 1 => t.betaRev #[mkConst ``Unit.unit]
        | _, _, _ => t
      trace[Meta.IndPredBelow.match] "oldCount = {oldCount}; fvars = {fvars}"
      let mut ctx := ctx
      for newDecl in newDecls do
        match newDecl with
        | .below decl indName vars =>
          for v in vars do
            ctx := { ctx with belows := ctx.belows.insert v (indName, decl.toExpr) }
        | .motive decl motiveIdx vars =>
          for v in vars do
            ctx := { ctx with motives := ctx.motives.insert v (motiveIdx, decl.toExpr) }
      let e' ← transformAlt ctx t
      let newAlt ← mkLambdaFVars fvars e'
      trace[Meta.IndPredBelow.match] "alt {idx}:\n{alt} ↦ {newAlt}"
      pure newAlt

  let newApp := mkApp res.matcher motive
  let newApp := mkAppN newApp discrs
  let newApp := mkAppN newApp alts
  return some (newApp, res.addMatcher)

where
  addBelowPattern (indName : Name) (idx : Nat) (lhs : AltLHS) : MetaM (AltLHS × Array NewDecl) := do
    withExistingLocalDecls lhs.fvarDecls do
    let prevPatterns := lhs.patterns.take idx
    let (originalPattern :: morePatterns) := lhs.patterns.drop idx |
      throwError "invalid amount of patterns"
    let ((predPattern, belowPattern), decls) ← (convertToBelow indName originalPattern none).run #[]
    let localDecls := (decls.map (·.getDecl)).toList
    withExistingLocalDecls localDecls do
    let patterns := prevPatterns ++ predPattern :: belowPattern :: morePatterns
    return ({ lhs with patterns, fvarDecls := lhs.fvarDecls ++ localDecls }, decls)

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
      StateRefT (Array NewDecl) MetaM (Pattern × Pattern) := do
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
          let (motiveIdx, realIdx) := recIdxs[i / 2]!
          trace[Meta.IndPredBelow.match] "transform {var} to {realIdx}, {belowFields[realIdx]!.toMessageData}"
          let (predPattern, belowPattern) ← convertToBelow belowInd belowFields[realIdx]! var
          belowFields := belowFields.set! realIdx predPattern
          -- add motive decl var
          let localDecl ← getFVarLocalDecl vars[i + 1]!
          let newDecl := .motive localDecl motiveIdx (collectDirectVarsInPattern predPattern)
          modify fun decls => decls.push newDecl
          belowFields := belowFields.push belowPattern
          belowFields := belowFields.push (.var vars[i + 1]!.fvarId!)
          i := i + 2
        let ctor := .ctor belowCtor.name us belowParams.toList belowFields.toList
        let ctorExpr ← originalPattern.toExpr
        return (.inaccessible ctorExpr, ctor)
    | .as varId p hId =>
      let (predPattern, belowPattern) ← convertToBelow belowIndName p var?
      return (.as varId predPattern hId, belowPattern)
    | _ =>
      -- variables, inaccessibles => just introduce below variable and keep original pattern
      let oldH ← originalPattern.toExpr
      if let some var := var? then
        let localDecl ← getFVarLocalDecl var
        let newDecl := .below localDecl belowIndName (collectDirectVarsInPattern originalPattern)
        modify fun decls => decls.push newDecl
        return (originalPattern, .var var.fvarId!)
      let tgtType ← toBelowType belowIndName oldH
      withLocalDeclD (← mkFreshUserName `h) tgtType fun newH => do
        let localDecl ← getFVarLocalDecl newH
        let newDecl := .below localDecl belowIndName (collectDirectVarsInPattern originalPattern)
        modify fun decls => decls.push newDecl
        return (originalPattern, .var newH.fvarId!)

builtin_initialize
  registerTraceClass `Meta.IndPredBelow
  registerTraceClass `Meta.IndPredBelow.match

end Lean.Meta.IndPredBelow
