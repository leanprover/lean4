/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.HeadIndex
import Lean.PrettyPrinter
import Lean.Util.FoldConsts
import Lean.Util.CollectFVars
import Lean.Meta.Basic
import Lean.Meta.InferType

namespace Lean.Meta.Grind

inductive Origin where
  /-- A global declaration in the environment. -/
  | decl (declName : Name)
  /-- A local hypothesis. -/
  | fvar (fvarId : FVarId)
  /--
  A proof term provided directly to a call to `grind` where `ref`
  is the provided grind argument. The `id` is a unique identifier for the call.
  -/
  | stx (id : Name) (ref : Syntax)
  | other
  deriving Inhabited, Repr

/-- A unique identifier corresponding to the origin. -/
def Origin.key : Origin → Name
  | .decl declName => declName
  | .fvar fvarId   => fvarId.name
  | .stx id _      => id
  | .other         => `other

def Origin.pp [Monad m] [MonadEnv m] [MonadError m] (o : Origin) : m MessageData := do
  match o with
  | .decl declName => return MessageData.ofConst (← mkConstWithLevelParams declName)
  | .fvar fvarId   => return mkFVar fvarId
  | .stx _ ref     => return ref
  | .other         => return "[unknown]"

/-- A theorem for heuristic instantiation based on E-matching. -/
structure EMatchTheorem where
  /--
  It stores universe parameter names for universe polymorphic proofs.
  Recall that it is non-empty only when we elaborate an expression provided by the user.
  When `proof` is just a constant, we can use the universe parameter names stored in the declaration.
  -/
  levelParams : Array Name
  proof       : Expr
  numParams   : Nat
  patterns    : List Expr
  /-- Contains all symbols used in `pattterns`. -/
  symbols     : List HeadIndex
  origin      : Origin
  deriving Inhabited

/-- The key is a symbol from `EMatchTheorem.symbols`. -/
abbrev EMatchTheorems := PHashMap Name (List EMatchTheorem)

def EMatchTheorems.insert (s : EMatchTheorems) (thm : EMatchTheorem) : EMatchTheorems := Id.run do
  let .const declName :: syms := thm.symbols
    | unreachable!
  let thm := { thm with symbols := syms }
  if let some thms := s.find? declName then
    return PersistentHashMap.insert s declName (thm::thms)
  else
    return PersistentHashMap.insert s declName [thm]

def EMatchTheorem.getProofWithFreshMVarLevels (thm : EMatchTheorem) : MetaM Expr := do
  if thm.proof.isConst && thm.levelParams.isEmpty then
    let declName := thm.proof.constName!
    let info ← getConstInfo declName
    if info.levelParams.isEmpty then
      return thm.proof
    else
      mkConstWithFreshMVarLevels declName
  else if thm.levelParams.isEmpty then
    return thm.proof
  else
    let us ← thm.levelParams.mapM fun _ => mkFreshLevelMVar
    return thm.proof.instantiateLevelParamsArray thm.levelParams us

private builtin_initialize ematchTheoremsExt : SimpleScopedEnvExtension EMatchTheorem EMatchTheorems ←
  registerSimpleScopedEnvExtension {
    addEntry := EMatchTheorems.insert
    initial  := .empty
  }

-- TODO: create attribute?
private def forbiddenDeclNames := #[``Eq, ``HEq, ``Iff, ``And, ``Or, ``Not]

private def isForbidden (declName : Name) := forbiddenDeclNames.contains declName

private def dontCare := mkConst (Name.mkSimple "[grind_dontcare]")

def mkGroundPattern (e : Expr) : Expr :=
  mkAnnotation `grind.ground_pat e

def groundPattern? (e : Expr) : Option Expr :=
  annotation? `grind.ground_pat e

private def isGroundPattern (e : Expr) : Bool :=
  groundPattern? e |>.isSome

def isPatternDontCare (e : Expr) : Bool :=
  e == dontCare

private def isAtomicPattern (e : Expr) : Bool :=
  e.isBVar || isPatternDontCare e || isGroundPattern e

partial def ppPattern (pattern : Expr) : MessageData := Id.run do
  if let some e := groundPattern? pattern then
    return m!"`[{e}]"
  else if isPatternDontCare pattern then
    return m!"?"
  else match pattern with
    | .bvar idx => return m!"#{idx}"
    | _ =>
      let mut r := m!"{pattern.getAppFn}"
      for arg in pattern.getAppArgs do
        let mut argFmt ← ppPattern arg
        if !isAtomicPattern arg then
          argFmt := MessageData.paren argFmt
        r := r ++ " " ++ argFmt
      return r

namespace NormalizePattern

structure State where
  symbols    : Array HeadIndex := #[]
  symbolSet  : Std.HashSet HeadIndex := {}
  bvarsFound : Std.HashSet Nat := {}

abbrev M := StateRefT State MetaM

private def saveSymbol (h : HeadIndex) : M Unit := do
  unless (← get).symbolSet.contains h do
    modify fun s => { s with symbols := s.symbols.push h, symbolSet := s.symbolSet.insert h }

private def foundBVar (idx : Nat) : M Bool :=
  return (← get).bvarsFound.contains idx

private def saveBVar (idx : Nat) : M Unit := do
  modify fun s => { s with bvarsFound := s.bvarsFound.insert idx }

private def getPatternFn? (pattern : Expr) : Option Expr :=
  if !pattern.isApp then
    none
  else match pattern.getAppFn with
    | f@(.const declName _) => if isForbidden declName then none else some f
    | f@(.fvar _) => some f
    | _ => none

/--
Returns a bit-mask `mask` s.t. `mask[i]` is true if the the corresponding argument is
- a type or type former, or
- a proof, or
- an instance implicit argument

When `mask[i]`, we say the corresponding argument is a "support" argument.
-/
private def getPatternFunMask (f : Expr) (numArgs : Nat) : MetaM (Array Bool) := do
  forallBoundedTelescope (← inferType f) numArgs fun xs _ => do
    xs.mapM fun x => do
      if (← isTypeFormer x <||> isProof x) then
        return true
      else
        return (← x.fvarId!.getDecl).binderInfo matches .instImplicit

private partial def go (pattern : Expr) (root := false) : M Expr := do
  if root && !pattern.hasLooseBVars then
    throwError "invalid pattern, it does not have pattern variables"
  let some f := getPatternFn? pattern
    | throwError "invalid pattern, (non-forbidden) application expected"
  assert! f.isConst || f.isFVar
  saveSymbol f.toHeadIndex
  let mut args := pattern.getAppArgs
  let supportMask ← getPatternFunMask f args.size
  for i in [:args.size] do
    let arg := args[i]!
    let isSupport := supportMask[i]?.getD false
    let arg ← if !arg.hasLooseBVars then
      if arg.hasMVar then
        pure dontCare
      else
        pure <| mkGroundPattern arg
    else match arg with
      | .bvar idx =>
        if isSupport && (← foundBVar idx) then
          pure dontCare
        else
          saveBVar idx
          pure arg
      | _ =>
        if isSupport then
          pure dontCare
        else if let some _ := getPatternFn? arg then
          go arg
        else
          pure dontCare
    args := args.set! i arg
  return mkAppN f args

def main (patterns : List Expr) : MetaM (List Expr × List HeadIndex × Std.HashSet Nat) := do
  let (patterns, s) ← patterns.mapM go |>.run {}
  return (patterns, s.symbols.toList, s.bvarsFound)

end NormalizePattern

/--
Returns `true` if free variables in `type` are not in `thmVars` or are in `fvarsFound`.
We use this function to check whether `type` is fully instantiated.
-/
private def checkTypeFVars (thmVars : FVarIdSet) (fvarsFound : FVarIdSet) (type : Expr) : Bool :=
  let typeFVars := (collectFVars {} type).fvarIds
  typeFVars.all fun fvarId => !thmVars.contains fvarId || fvarsFound.contains fvarId

/--
Given an type class instance type `instType`, returns true if free variables in input parameters
1- are not in `thmVars`, or
2- are in `fvarsFound`.
Remark: `fvarsFound` is a subset of `thmVars`
-/
private def canBeSynthesized (thmVars : FVarIdSet) (fvarsFound : FVarIdSet) (instType : Expr) : MetaM Bool := do
  forallTelescopeReducing instType fun xs type => type.withApp fun classFn classArgs => do
    for x in xs do
      unless checkTypeFVars thmVars fvarsFound (← inferType x) do return false
    forallBoundedTelescope (← inferType classFn) type.getAppNumArgs fun params _ => do
      for param in params, classArg in classArgs do
        let paramType ← inferType param
        if !paramType.isAppOf ``semiOutParam && !paramType.isAppOf ``outParam then
          unless checkTypeFVars thmVars fvarsFound classArg do
            return false
      return true

/--
Auxiliary type for the `checkCoverage` function.
-/
inductive CheckCoverageResult where
  | /-- `checkCoverage` succeeded -/
    ok
  | /--
    `checkCoverage` failed because some of the theorem parameters are missing,
    `pos` contains their positions
    -/
    missing (pos : List Nat)

/--
After we process a set of patterns, we obtain the set of de Bruijn indices in these patterns.
We say they are pattern variables. This function checks whether the set of pattern variables is sufficient for
instantiating the theorem with proof `thmProof`. The theorem has `numParams` parameters.
The missing parameters:
1- we may be able to infer them using type inference or type class synthesis, or
2- they are propositions, and may become hypotheses of the instantiated theorem.

For type class instance parameters, we must check whether the free variables in class input parameters are available.
-/
private def checkCoverage (thmProof : Expr) (numParams : Nat) (bvarsFound : Std.HashSet Nat) : MetaM CheckCoverageResult := do
  if bvarsFound.size == numParams then return .ok
  forallBoundedTelescope (← inferType thmProof) numParams fun xs _ => do
    assert! numParams == xs.size
    let patternVars := bvarsFound.toList.map fun bidx => xs[numParams - bidx - 1]!.fvarId!
    -- `xs` as a `FVarIdSet`.
    let thmVars : FVarIdSet := RBTree.ofList <| xs.toList.map (·.fvarId!)
    -- Collect free variables occurring in `e`, and insert the ones that are in `thmVars` into `fvarsFound`
    let update (fvarsFound : FVarIdSet) (e : Expr) : FVarIdSet :=
      (collectFVars {} e).fvarIds.foldl (init := fvarsFound) fun s fvarId =>
        if thmVars.contains fvarId then s.insert fvarId else s
    -- Theorem variables found so far. We initialize with the variables occurring in patterns
    -- Remark: fvarsFound is a subset of thmVars
    let mut fvarsFound : FVarIdSet := RBTree.ofList patternVars
    for patternVar in patternVars do
      let type ← patternVar.getType
      fvarsFound := update fvarsFound type
    if fvarsFound.size == numParams then return .ok
    -- Now, we keep traversing remaining variables and collecting
    -- `processed` contains the variables we have already processed.
    let mut processed : FVarIdSet := RBTree.ofList patternVars
    let mut modified := false
    repeat
      modified := false
      for x in xs do
        let fvarId := x.fvarId!
        unless processed.contains fvarId do
          let xType ← inferType x
          if fvarsFound.contains fvarId then
            -- Collect free vars in `x`s type and mark as processed
            fvarsFound := update fvarsFound xType
            processed := processed.insert fvarId
            modified := true
          else if (← isProp xType) then
            -- If `x` is a proposition, and all theorem variables in `x`s type have already been found
            -- add it to `fvarsFound` and mark it as processed.
            if checkTypeFVars thmVars fvarsFound xType then
              fvarsFound := fvarsFound.insert fvarId
              processed := processed.insert fvarId
              modified := true
          else if (← fvarId.getDecl).binderInfo matches .instImplicit then
            -- If `x` is instance implicit, check whether
            -- we have found all free variables needed to synthesize instance
            if (← canBeSynthesized thmVars fvarsFound xType) then
              fvarsFound := fvarsFound.insert fvarId
              fvarsFound := update fvarsFound xType
              processed := processed.insert fvarId
              modified := true
      if fvarsFound.size == numParams then
        return .ok
      if !modified then
        break
    let mut pos := #[]
    for h : i in [:xs.size] do
      let fvarId := xs[i].fvarId!
      unless fvarsFound.contains fvarId do
        pos := pos.push i
    return .missing pos.toList

/--
Given a theorem with proof `proof` and `numParams` parameters, returns a message
containing the parameters at positions `paramPos`.
-/
private def ppParamsAt (proof : Expr) (numParms : Nat) (paramPos : List Nat) : MetaM MessageData := do
  forallBoundedTelescope (← inferType proof) numParms fun xs _ => do
    let mut msg := m!""
    let mut first := true
    for h : i in [:xs.size] do
      if paramPos.contains i then
        let x := xs[i]
        if first then first := false else msg := msg ++ "\n"
        msg := msg ++ m!"{x} : {← inferType x}"
    addMessageContextFull msg

def addEMatchTheorem (declName : Name) (numParams : Nat) (patterns : List Expr) : MetaM Unit := do
  let .thmInfo info ← getConstInfo declName
    | throwError "`{declName}` is not a theorem, you cannot assign patterns to non-theorems for the `grind` tactic"
  let us := info.levelParams.map mkLevelParam
  let proof := mkConst declName us
  let (patterns, symbols, bvarFound) ← NormalizePattern.main patterns
  assert! symbols.all fun s => s matches .const _
  trace[grind.ematch.pattern] "{declName}: {patterns.map ppPattern}"
  if let .missing pos ← checkCoverage proof numParams bvarFound then
     let pats : MessageData := m!"{patterns.map ppPattern}"
     throwError "invalid pattern(s) for `{declName}`{indentD pats}\nthe following theorem parameters cannot be instantiated:{indentD (← ppParamsAt proof numParams pos)}"
  ematchTheoremsExt.add {
     proof, patterns, numParams, symbols
     levelParams := #[]
     origin      := .decl declName
  }

/--
Given theorem with name `declName` and type of the form `∀ (a_1 ... a_n), lhs = rhs`,
add an E-matching pattern for it using `addEMatchTheorem n [lhs]`
-/
def addEMatchEqTheorem (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let (numParams, patterns) ← forallTelescopeReducing info.type fun xs type => do
    let_expr Eq _ lhs _ := type | throwError "invalid E-matching equality theorem, conclusion must be an equality{indentExpr type}"
    return (xs.size, [lhs.abstract xs])
  addEMatchTheorem declName numParams patterns

def getEMatchTheorems : CoreM EMatchTheorems :=
  return ematchTheoremsExt.getState (← getEnv)

end Lean.Meta.Grind
