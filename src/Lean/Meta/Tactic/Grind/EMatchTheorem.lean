/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Init.Grind.Tactics
import Lean.HeadIndex
import Lean.PrettyPrinter
import Lean.Util.FoldConsts
import Lean.Util.CollectFVars
import Lean.Meta.Basic
import Lean.Meta.InferType
import Lean.Meta.Eqns
import Lean.Meta.Tactic.Grind.Util

namespace Lean.Meta.Grind

def mkOffsetPattern (pat : Expr) (k : Nat) : Expr :=
  mkApp2 (mkConst ``Grind.offset) pat (mkRawNatLit k)

private def detectOffsets (pat : Expr) : MetaM Expr := do
  let pre (e : Expr) := do
    if e == pat then
      -- We only consider nested offset patterns
      return .continue e
    else match e with
      | .letE .. | .lam .. | .forallE .. => return .done e
      | _ =>
        let some (e, k) ← isOffset? e
          | return .continue e
        if k == 0 then return .continue e
        return .continue <| mkOffsetPattern e k
  Core.transform pat (pre := pre)

def isOffsetPattern? (pat : Expr) : Option (Expr × Nat) := Id.run do
  let_expr Grind.offset pat k := pat | none
  let .lit (.natVal k) := k | none
  return some (pat, k)

def preprocessPattern (pat : Expr) (normalizePattern := true) : MetaM Expr := do
  let pat ← instantiateMVars pat
  let pat ← unfoldReducible pat
  let pat ← if normalizePattern then normalize pat else pure pat
  let pat ← detectOffsets pat
  let pat ← foldProjs pat
  return pat

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

/-- Set of E-matching theorems. -/
structure EMatchTheorems where
  /-- The key is a symbol from `EMatchTheorem.symbols`. -/
  private map : PHashMap Name (List EMatchTheorem) := {}
  /-- Set of theorem names that have been inserted using `insert`. -/
  private thmNames : PHashSet Name := {}
  deriving Inhabited

/--
Inserts a `thm` with symbols `[s_1, ..., s_n]` to `s`.
We add `s_1 -> { thm with symbols := [s_2, ..., s_n] }`.
When `grind` internalizes a term containing symbol `s`, we
process all theorems `thm` associated with key `s`.
If their `thm.symbols` is empty, we say they are activated.
Otherwise, we reinsert into `map`.
-/
def EMatchTheorems.insert (s : EMatchTheorems) (thm : EMatchTheorem) : EMatchTheorems := Id.run do
  let .const declName :: syms := thm.symbols
    | unreachable!
  let thm := { thm with symbols := syms }
  let { map, thmNames } := s
  let thmNames := thmNames.insert thm.origin.key
  if let some thms := map.find? declName then
    return { map := map.insert declName (thm::thms), thmNames }
  else
    return { map := map.insert declName [thm], thmNames }

/--
Retrieves theorems from `s` associated with the given symbol. See `EMatchTheorem.insert`.
The theorems are removed from `s`.
-/
@[inline]
def EMatchTheorems.retrieve? (s : EMatchTheorems) (sym : Name) : Option (List EMatchTheorem × EMatchTheorems) :=
  if let some thms := s.map.find? sym then
    some (thms, { s with map := s.map.erase sym })
  else
    none

/-- Returns `true` if `declName` is the name of a theorem that was inserted using `insert`. -/
def EMatchTheorems.containsTheoremName (s : EMatchTheorems) (declName : Name) : Bool :=
  s.thmNames.contains declName

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
    initial  := {}
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
- a type (that is not a proposition) or type former, or
- a proof, or
- an instance implicit argument

When `mask[i]`, we say the corresponding argument is a "support" argument.
-/
def getPatternSupportMask (f : Expr) (numArgs : Nat) : MetaM (Array Bool) := do
  forallBoundedTelescope (← inferType f) numArgs fun xs _ => do
    xs.mapM fun x => do
      if (← isProp x) then
        return false
      else if (← isTypeFormer x <||> isProof x) then
        return true
      else
        return (← x.fvarId!.getDecl).binderInfo matches .instImplicit

private partial def go (pattern : Expr) (root := false) : M Expr := do
  if root && !pattern.hasLooseBVars then
    throwError "invalid pattern, it does not have pattern variables"
  if let some (e, k) := isOffsetPattern? pattern then
    let e ← goArg e (isSupport := false)
    if e == dontCare then
      return dontCare
    else
      return mkOffsetPattern e k
  let some f := getPatternFn? pattern
    | throwError "invalid pattern, (non-forbidden) application expected{indentExpr pattern}"
  assert! f.isConst || f.isFVar
  saveSymbol f.toHeadIndex
  let mut args := pattern.getAppArgs
  let supportMask ← getPatternSupportMask f args.size
  for i in [:args.size] do
    let arg := args[i]!
    let isSupport := supportMask[i]?.getD false
    args := args.set! i (← goArg arg isSupport)
  return mkAppN f args
where
  goArg (arg : Expr) (isSupport : Bool) : M Expr := do
    if !arg.hasLooseBVars then
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

def main (patterns : List Expr) : MetaM (List Expr × List HeadIndex × Std.HashSet Nat) := do
  let (patterns, s) ← patterns.mapM go |>.run {}
  return (patterns, s.symbols.toList, s.bvarsFound)

def normalizePattern (e : Expr) : M Expr := do
  go e

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
private def ppParamsAt (proof : Expr) (numParams : Nat) (paramPos : List Nat) : MetaM MessageData := do
  forallBoundedTelescope (← inferType proof) numParams fun xs _ => do
    let mut msg := m!""
    let mut first := true
    for h : i in [:xs.size] do
      if paramPos.contains i then
        let x := xs[i]
        if first then first := false else msg := msg ++ "\n"
        msg := msg ++ m!"{x} : {← inferType x}"
    addMessageContextFull msg

/--
Creates an E-matching theorem for a theorem with proof `proof`, `numParams` parameters, and the given set of patterns.
Pattern variables are represented using de Bruijn indices.
-/
def mkEMatchTheoremCore (origin : Origin) (levelParams : Array Name) (numParams : Nat) (proof : Expr) (patterns : List Expr) : MetaM EMatchTheorem := do
  let (patterns, symbols, bvarFound) ← NormalizePattern.main patterns
  trace[grind.ematch.pattern] "{MessageData.ofConst proof}: {patterns.map ppPattern}"
  if let .missing pos ← checkCoverage proof numParams bvarFound then
     let pats : MessageData := m!"{patterns.map ppPattern}"
     throwError "invalid pattern(s) for `{← origin.pp}`{indentD pats}\nthe following theorem parameters cannot be instantiated:{indentD (← ppParamsAt proof numParams pos)}"
  return {
    proof, patterns, numParams, symbols
    levelParams, origin
  }

private def getProofFor (declName : Name) : CoreM Expr := do
  let .thmInfo info ← getConstInfo declName
    | throwError "`{declName}` is not a theorem"
  let us := info.levelParams.map mkLevelParam
  return mkConst declName us

/--
Creates an E-matching theorem for `declName` with `numParams` parameters, and the given set of patterns.
Pattern variables are represented using de Bruijn indices.
-/
def mkEMatchTheorem (declName : Name) (numParams : Nat) (patterns : List Expr) : MetaM EMatchTheorem := do
  mkEMatchTheoremCore (.decl declName) #[] numParams (← getProofFor declName) patterns

/--
Given a theorem with proof `proof` and type of the form `∀ (a_1 ... a_n), lhs = rhs`,
creates an E-matching pattern for it using `addEMatchTheorem n [lhs]`
If `normalizePattern` is true, it applies the `grind` simplification theorems and simprocs to the pattern.
-/
def mkEMatchEqTheoremCore (origin : Origin) (levelParams : Array Name) (proof : Expr) (normalizePattern : Bool) : MetaM EMatchTheorem := do
  let (numParams, patterns) ← forallTelescopeReducing (← inferType proof) fun xs type => do
    let lhs ← match_expr type with
      | Eq _ lhs _ => pure lhs
      | Iff lhs _ => pure lhs
      | HEq _ lhs _ _ => pure lhs
      | _ => throwError "invalid E-matching equality theorem, conclusion must be an equality{indentExpr type}"
    let lhs ← preprocessPattern lhs normalizePattern
    return (xs.size, [lhs.abstract xs])
  mkEMatchTheoremCore origin levelParams numParams proof patterns

/--
Given theorem with name `declName` and type of the form `∀ (a_1 ... a_n), lhs = rhs`,
creates an E-matching pattern for it using `addEMatchTheorem n [lhs]`

If `normalizePattern` is true, it applies the `grind` simplification theorems and simprocs to the
pattern.
-/
def mkEMatchEqTheorem (declName : Name) (normalizePattern := true) : MetaM EMatchTheorem := do
  mkEMatchEqTheoremCore (.decl declName) #[] (← getProofFor declName) normalizePattern

/--
Adds an E-matching theorem to the environment.
See `mkEMatchTheorem`.
-/
def addEMatchTheorem (declName : Name) (numParams : Nat) (patterns : List Expr) : MetaM Unit := do
  ematchTheoremsExt.add (← mkEMatchTheorem declName numParams patterns)

/--
Adds an E-matching equality theorem to the environment.
See `mkEMatchEqTheorem`.
-/
def addEMatchEqTheorem (declName : Name) : MetaM Unit := do
  ematchTheoremsExt.add (← mkEMatchEqTheorem declName)

/-- Returns the E-matching theorems registered in the environment. -/
def getEMatchTheorems : CoreM EMatchTheorems :=
  return ematchTheoremsExt.getState (← getEnv)

private inductive TheoremKind where
  | eq | fwd | bwd | default
  deriving Inhabited, BEq

private def TheoremKind.toAttribute : TheoremKind → String
  | .eq      => "[grind =]"
  | .fwd     => "[grind →]"
  | .bwd     => "[grind ←]"
  | .default => "[grind]"

private def TheoremKind.explainFailure : TheoremKind → String
  | .eq      => "failed to find pattern in the left-hand side of the theorem's conclusion"
  | .fwd     => "failed to find patterns in the antecedents of the theorem"
  | .bwd     => "failed to find patterns in the theorem's conclusion"
  | .default => "failed to find patterns"

/-- Returns the types of `xs` that are propositions. -/
private def getPropTypes (xs : Array Expr) : MetaM (Array Expr) :=
  xs.filterMapM fun x => do
    let type ← inferType x
    if (← isProp type) then return some type else return none

/-- State for the (pattern) `CollectorM` monad -/
private structure Collector.State where
  /-- Pattern found so far. -/
  patterns  : Array Expr := #[]
  done      : Bool := false

private structure Collector.Context where
  proof : Expr
  xs    : Array Expr

/-- Monad for collecting patterns for a theorem. -/
private abbrev CollectorM := ReaderT Collector.Context $ StateRefT Collector.State NormalizePattern.M

/-- Similar to `getPatternFn?`, but operates on expressions that do not contain loose de Bruijn variables. -/
private def isPatternFnCandidate (f : Expr) : CollectorM Bool := do
  match f with
  | .const declName _ => return !isForbidden declName
  | .fvar .. => return !(← read).xs.contains f
  | _ => return false

private def addNewPattern (p : Expr) : CollectorM Unit := do
  trace[grind.ematch.pattern.search] "found pattern: {ppPattern p}"
  let bvarsFound := (← getThe NormalizePattern.State).bvarsFound
  let done := (← checkCoverage (← read).proof (← read).xs.size bvarsFound) matches .ok
  if done then
    trace[grind.ematch.pattern.search] "found full coverage"
  modify fun s => { s with patterns := s.patterns.push p, done }

private partial def collect (e : Expr) : CollectorM Unit := do
  if (← get).done then return ()
  match e with
  | .app .. =>
    let f := e.getAppFn
    if (← isPatternFnCandidate f) then
      let saved ← getThe NormalizePattern.State
      try
        trace[grind.ematch.pattern.search] "candidate: {e}"
        let p := e.abstract (← read).xs
        unless p.hasLooseBVars do
          trace[grind.ematch.pattern.search] "skip, does not contain pattern variables"
          return ()
        let p ← NormalizePattern.normalizePattern p
        if saved.bvarsFound.size < (← getThe NormalizePattern.State).bvarsFound.size then
          addNewPattern p
          return ()
        trace[grind.ematch.pattern.search] "skip, no new variables covered"
        -- restore state and continue search
        set saved
      catch _ =>
        -- restore state and continue search
        trace[grind.ematch.pattern.search] "skip, exception during normalization"
        set saved
    let args := e.getAppArgs
    for arg in args, flag in (← NormalizePattern.getPatternSupportMask f args.size) do
      unless flag do
        collect arg
  | .forallE _ d b _ =>
    if (← pure e.isArrow <&&> isProp d <&&> isProp b) then
      collect d
      collect b
  | _ => return ()

private def collectPatterns? (proof : Expr) (xs : Array Expr) (searchPlaces : Array Expr) : MetaM (Option (List Expr × List HeadIndex)) := do
  let go : CollectorM (Option (List Expr)) := do
    for place in searchPlaces do
      let place ← preprocessPattern place
      collect place
      if (← get).done then
        return some ((← get).patterns.toList)
    return none
  let (some ps, s) ← go { proof, xs } |>.run' {} |>.run {}
    | return none
  return some (ps, s.symbols.toList)

private def mkEMatchTheoremWithKind? (origin : Origin) (levelParams : Array Name) (proof : Expr) (kind : TheoremKind) : MetaM (Option EMatchTheorem) := do
  if kind == .eq then
    return (← mkEMatchEqTheoremCore origin levelParams proof false)
  let type ← inferType proof
  forallTelescopeReducing type fun xs type => do
    let searchPlaces ← match kind with
      | .fwd =>
        let ps ← getPropTypes xs
        if ps.isEmpty then
          throwError "invalid `grind` forward theorem, theorem `{← origin.pp}` does not have proposional hypotheses"
        pure ps
      | .bwd => pure #[type]
      | .default => pure <| #[type] ++ (← getPropTypes xs)
      | .eq => unreachable!
    go xs searchPlaces
where
  go (xs : Array Expr) (searchPlaces : Array Expr) : MetaM (Option EMatchTheorem) := do
    let some (patterns, symbols) ← collectPatterns? proof xs searchPlaces
      | return none
    let numParams := xs.size
    trace[grind.ematch.pattern] "{← origin.pp}: {patterns.map ppPattern}"
    return some {
      proof, patterns, numParams, symbols
      levelParams, origin
    }

private def getKind (stx : Syntax) : TheoremKind :=
  if stx[1].isNone then
    .default
  else if stx[1][0].getKind == ``Parser.Attr.grindEq then
    .eq
  else if stx[1][0].getKind == ``Parser.Attr.grindFwd then
    .fwd
  else
    .bwd

private def addGrindEqAttr (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  if (← getConstInfo declName).isTheorem then
    ematchTheoremsExt.add (← mkEMatchEqTheorem declName) attrKind
  else if let some eqns ← getEqnsFor? declName then
    for eqn in eqns do
      ematchTheoremsExt.add (← mkEMatchEqTheorem eqn) attrKind
  else
    throwError "`[grind_eq]` attribute can only be applied to equational theorems or function definitions"

private def addGrindAttr (declName : Name) (attrKind : AttributeKind) (thmKind : TheoremKind) : MetaM Unit := do
  if thmKind == .eq then
    addGrindEqAttr declName attrKind
  else if !(← getConstInfo declName).isTheorem then
    addGrindEqAttr declName attrKind
  else
    let some thm ← mkEMatchTheoremWithKind? (.decl declName) #[] (← getProofFor declName) thmKind
      | throwError "`@{thmKind.toAttribute} theorem {declName}` {thmKind.explainFailure}, consider using different options or the `grind_pattern` command"
    ematchTheoremsExt.add thm attrKind

builtin_initialize
  registerBuiltinAttribute {
    name := `grind
    descr :=
      "The `[grind_eq]` attribute is used to annotate equational theorems and functions.\
      When applied to an equational theorem, it marks the theorem for use in heuristic instantiations by the `grind` tactic.\
      When applied to a function, it automatically annotates the equational theorems associated with that function.\
      The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.\
      For example, if a theorem `@[grind_eq] theorem foo_idempotent : foo (foo x) = foo x` is annotated,\
      `grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."
    applicationTime := .afterCompilation
    add := fun declName stx attrKind => do
      addGrindAttr declName attrKind (getKind stx) |>.run' {}
  }

end Lean.Meta.Grind
