/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Extension
import Init.Grind.Util
import Lean.Util.ForEachExpr
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Match.Basic
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Sym.Util
public section
namespace Lean.Meta.Grind
/-!
## Design Note: Symbol Priorities and Extension State

We considered including `SymbolPriorities` in `ExtensionState` to allow each `grind` attribute/extension
to define its own symbol priorities. However, this design was rejected because E-match patterns are selected
with respect to symbol priorities. When using multiple `grind` attributes simultaneously
(e.g., `grind only [attr_1, attr_2]`), patterns would need to be re-selected using the union of all
symbol priorities and then re-normalized using the union of all normalizers, an expensive operation we want to avoid.

Instead, we use a single global `SymbolPriorities` set shared across all `grind` attributes.
See also: the related note in `Extension.lean` regarding normalization.
-/

structure SymbolPriorityEntry where
  declName : Name
  prio : Nat
  deriving Inhabited

/-- Removes the given declaration from `s`. -/
def SymbolPriorities.erase (s : SymbolPriorities) (declName : Name) : SymbolPriorities :=
  { s with map := s.map.erase declName }

/-- Returns `declName` priority for E-matching pattern inference in `s`. -/
def SymbolPriorities.getPrio (s : SymbolPriorities) (declName : Name) : Nat :=
  if let some prio := s.map.find? declName then
    prio
  else
    eval_prio default

/--
Returns `true`, if there is an entry `declName ↦ prio` in `s`.
Recall that symbols not in `s` are assumed to have default priority.
-/
def SymbolPriorities.contains (s : SymbolPriorities) (declName : Name) : Bool :=
  s.map.contains declName

private builtin_initialize symbolPrioExt : SimpleScopedEnvExtension SymbolPriorityEntry SymbolPriorities ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := fun s {declName, prio} => s.insert declName prio
  }

def resetSymbolPrioExt : CoreM Unit := do
  modifyEnv fun env => symbolPrioExt.modifyState env fun _ => {}

def getGlobalSymbolPriorities : CoreM SymbolPriorities :=
  return symbolPrioExt.getState (← getEnv)

/-- Sets `declName` priority to be used during E-matching pattern inference -/
def addSymbolPriorityAttr (declName : Name) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  symbolPrioExt.add { declName, prio } attrKind

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

/--
`detectOffsets` inverse.
This function is used to expand `mkOffsetPattern` occurring in a constant pattern.
-/
private def expandOffsetPatterns (pat : Expr) : CoreM Expr := do
  let pre (e : Expr) := do
    match e with
    | .letE .. | .lam .. | .forallE .. => return .done e
    | _ =>
      let some (e, k) := isOffsetPattern? e
        | return .continue e
      if k == 0 then return .continue e
      return .continue <| mkNatAdd e (mkNatLit k)
  Core.transform pat (pre := pre)

def mkEqBwdPattern (u : List Level) (α : Expr) (lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``Grind.eqBwdPattern u) α lhs rhs

def isEqBwdPattern (e : Expr) : Bool :=
  e.isAppOfArity ``Grind.eqBwdPattern 3

def isEqBwdPattern? (e : Expr) : Option (Expr × Expr) :=
  let_expr Grind.eqBwdPattern _ lhs rhs := e
    | none
  some (lhs, rhs)

def mkGenPattern (u : List Level) (α : Expr) (h : Expr) (x : Expr) (val : Expr) : Expr :=
  mkApp4 (mkConst ``Grind.genPattern u) α h x val

def mkGenHEqPattern (u : List Level) (α β : Expr) (h : Expr) (x : Expr) (val : Expr) : Expr :=
  mkApp5 (mkConst ``Grind.genHEqPattern u) α β h x val

/-- Generalized pattern information. See `Grind.genPattern` gadget. -/
structure GenPatternInfo where
  heq  : Bool
  hIdx : Nat
  xIdx : Nat
  deriving Repr

def isGenPattern? (pat : Expr) : Option (GenPatternInfo × Expr) :=
  match_expr pat with
  | Grind.genPattern _ h x pat => Id.run do
    let .bvar hIdx := h | unreachable!
    let .bvar xIdx := x | unreachable!
    return some ({ heq := false, hIdx, xIdx }, pat )
  | Grind.genHEqPattern _ _ h x pat => Id.run do
    let .bvar hIdx := h | unreachable!
    let .bvar xIdx := x | unreachable!
    return some ({ heq := true, hIdx, xIdx }, pat )
  | _ => none

/-- Returns `true` if `declName` is the name of a `match`-expression congruence equation. -/
def isMatchCongrEqDeclName (declName : Name) : CoreM Bool := do
  match declName with
  | .str p s =>
    pure (Match.isCongrEqnReservedNameSuffix s) <&&>
      -- `declName` was formed by `mkPrivateName _ matcherName` but as `matcherName` may or may not
      -- have already been private, there is no direct way to invert this function; so we try both
      -- possibilities (at most one of them can exist).
      (isMatcher p <||> isMatcher (privateToUserName p))
  | _ => return false

/-- Returns `true` if `e` is a constant for a `match`-expression congruence equation. -/
private def isMatchCongrEqConst (e : Expr) : CoreM Bool := do
  let .const declName _ := e | return false
  isMatchCongrEqDeclName declName

/--
Given the type of a `match` congruence equation, annotate the discriminants using
the gadgets `Grind.genPattern` and `Grind.genHEqPattern`.
For example, consider the following `match` congruence theorem type
```
forall
  (motive : Option Nat → Sort u_1) (a✝ : Option Nat)
  (h_1 : a✝ = none → motive none)
  (h_2 : (val : Nat) → a✝ = some val → motive (some val))
  (val✝ : Nat)
  (heq_1 : a✝ = some val✝),
  g.match_1 motive a✝ h_1 h_2 ≍ h_2 val✝ heq_1
```
This function returns the type
```
forall
  (motive : Option Nat → Sort u_1) (a✝ : Option Nat)
  (h_1 : a✝ = none → motive none)
  (h_2 : (val : Nat) → a✝ = some val → motive (some val))
  (val✝ : Nat)
  (heq_1 : a✝ = some val✝),
  g.match_1 motive (Grind.genPattern (Option Nat) heq_1 a✝ (some val✝)) h_1 h_2
  ≍ h_2 val✝ heq_1
```
The gadget is used to infer a `generalize` pattern. The following term is used
during E-matching `g.match_1 motive (Grind.genPattern (Option Nat) heq_1 a✝ (some val✝)) h_1 h_2`
when matching `Grind.genPattern (Option Nat) heq_1 a✝ (some val✝)` the matcher uses
`(some val✝)` as the actual pattern, but also assigns `heq_1` `a✝` using the information stored
in the equivalence class.
-/
private def preprocessMatchCongrEqType (type : Expr) : MetaM Expr := do
  forallTelescopeReducing type fun hs resultType => do
    let lhs ← match_expr resultType with
      | Eq _ lhs _ => pure lhs
      | HEq _ lhs _ _ => pure lhs
      | _ => return type
    let lhsFn := lhs.getAppFn
    let .const declName _ := lhsFn | return type
    let some matcherInfo ← getMatcherInfo? declName | return type
    let range := matcherInfo.getDiscrRange
    let mut args := lhs.getAppArgs
    for h in hs do
      match_expr (← inferType h) with
      | f@Eq α lhs rhs =>
        for i in range do
          if lhs == args[i]! then
            args := args.set! i (mkGenPattern f.constLevels! α h lhs rhs)
            break
      | f@HEq α lhs β rhs =>
        for i in range do
          if lhs == args[i]! then
            args := args.set! i (mkGenHEqPattern f.constLevels! α β h lhs rhs)
            break
      | _ => pure ()
    let lhsNew := mkAppN lhsFn args
    let resultTypeFn := resultType.getAppFn
    let resultArgs := resultType.getAppArgs
    let resultType := mkAppN resultTypeFn (resultArgs.set! 1 lhsNew)
    mkForallFVars hs resultType

/--
A heuristic procedure for detecting generalized patterns.
For example, given the theorem
```
theorem Option.pbind_some' {α β} {x : Option α} {a : α} {f : (a : α) → x = some a → Option β}
  (h : x = some a) : pbind x f = f a h
```
In the current implementation, we support only occurrences in the resulting type.
Thus, the following resulting type is generated for the example above:
```
pbind (Grind.genPattern h x (some a)) f = f a h
```
-/
private def detectGeneralizedPatterns? (type : Expr) : MetaM Expr := do
  -- `genPattern` is not necessarily referenced in the result but always importing it for `grind`
  -- uses is a solid approximation.
  recordExtraModUseFromDecl (isMeta := false) ``Grind.genPattern
  forallTelescopeReducing type fun hs resultType => do
    let isTarget? (lhs : Expr) (rhs : Expr) (s : FVarSubst) : Option (FVarId × Expr) := Id.run do
      let .fvar fvarId := lhs | return none
      if !hs.contains lhs then
        return none -- It is a foreign free variable
      if rhs.containsFVar fvarId then
        return none -- It is not a generalization if `rhs` contains it
      if s.contains fvarId then
        return none -- Remark: may want to abort instead, it is probably not a generalization
      let rhs := s.apply rhs
      return some (fvarId, rhs)
    let mut s : FVarSubst := {}
    for h in hs do
      match_expr (← inferType h) with
      | f@Eq α lhs rhs =>
        let some (fvarId, rhs) := isTarget? lhs rhs s | pure ()
        s := s.insert fvarId <| mkGenPattern f.constLevels! α h lhs rhs
      | f@HEq α lhs β rhs =>
        let some (fvarId, rhs) := isTarget? lhs rhs s | pure ()
        s := s.insert fvarId <| mkGenHEqPattern f.constLevels! α β h lhs rhs
      | _ => pure ()
    if s.isEmpty then
      return type
    let resultType' := s.apply resultType
    if resultType' == resultType then
      return type
    mkForallFVars hs resultType'

/--
Given the proof for a proposition to be used as an E-matching theorem,
infers its type, and preprocess it to identify generalized patterns.
Recall that we infer these generalized patterns automatically for
`match` congruence equations.
-/
private def inferEMatchProofType (proof : Expr) (gen : Bool) : MetaM Expr := do
  let type ← inferType proof
  if (← isMatchCongrEqConst proof) then
    preprocessMatchCongrEqType type
  else if gen then
    detectGeneralizedPatterns? type
  else
    return type

-- Configuration for the `grind` normalizer. We want both `zetaDelta` and `zeta`
private def normConfig : Grind.Config := {}
private theorem normConfig_zeta : normConfig.zeta = true := rfl
private theorem normConfig_zetaDelta : normConfig.zetaDelta = true := rfl

def preprocessPattern (pat : Expr) (normalizePattern := true) : MetaM Expr := do
  let pat ← instantiateMVars pat
  let pat ← Sym.unfoldReducible pat
  let pat ← if normalizePattern then normalize pat normConfig else pure pat
  let pat ← detectOffsets pat
  let pat ← foldProjs pat
  return pat

def EMatchTheoremKind.isEqLhs : EMatchTheoremKind → Bool
  | .eqLhs _ => true
  | _ => false

def EMatchTheoremKind.isDefault : EMatchTheoremKind → Bool
  | .default _ => true
  | _ => false

def EMatchTheoremKind.toAttributeCore (kind : EMatchTheoremKind) : String :=
  match kind with
  | .eqLhs true     => "= gen"
  | .eqLhs false    => "="
  | .eqRhs true     => "=_ gen"
  | .eqRhs false    => "=_"
  | .eqBoth false   => "_=_"
  | .eqBoth true    => "_=_ gen"
  | .eqBwd          => "←="
  | .fwd            => "→"
  | .bwd false      => "←"
  | .bwd true       => "← gen"
  | .leftRight      => "=>"
  | .rightLeft      => "<="
  | .default false  => "."
  | .default true   => ". gen"
  | .user           => ""

def EMatchTheoremKind.toAttribute (k : EMatchTheoremKind) (minIndexable : Bool): String :=
  if k matches .user then
    "[grind]"
  else if minIndexable then
    s!"[grind! {toAttributeCore k}]"
  else
    s!"[grind {toAttributeCore k}]"

private def EMatchTheoremKind.explainFailure : EMatchTheoremKind → String
  | .eqLhs _   => "failed to find pattern in the left-hand side of the theorem's conclusion"
  | .eqRhs _   => "failed to find pattern in the right-hand side of the theorem's conclusion"
  | .eqBoth _  => unreachable! -- eqBoth is a macro
  | .eqBwd     => "failed to use theorem's conclusion as a pattern"
  | .fwd       => "failed to find patterns in the antecedents of the theorem"
  | .bwd _     => "failed to find patterns in the theorem's conclusion"
  | .leftRight => "failed to find patterns searching from left to right"
  | .rightLeft => "failed to find patterns searching from right to left"
  | .default _ => "failed to find patterns"
  | .user      => unreachable!


/-- Set of E-matching theorems. -/
abbrev EMatchTheorems := Theorems EMatchTheorem

/-- A collection of sets of E-matching theorems. -/
abbrev EMatchTheoremsArray := TheoremsArray EMatchTheorem

/--
Returns `true` if there is a theorem with exactly the same pattern and constraints is already in `s`
-/
def EMatchTheorems.containsWithSamePatterns (s : EMatchTheorems) (origin : Origin)
    (patterns : List Expr) (cnstrs : List EMatchTheoremConstraint) : Bool :=
  let thms := s.find origin
  thms.any fun thm => thm.patterns == patterns && thm.cnstrs == cnstrs

def ExtensionStateArray.containsWithSamePatterns (s : ExtensionStateArray) (origin : Origin)
    (patterns : List Expr) (cnstrs : List EMatchTheoremConstraint) : Bool :=
  s.any (EMatchTheorems.containsWithSamePatterns ·.ematch origin patterns cnstrs)

def EMatchTheorems.getKindsFor (s : EMatchTheorems) (origin : Origin) : List EMatchTheoremKind :=
  let thms := s.find origin
  thms.map (·.kind)

def EMatchTheorem.getProofWithFreshMVarLevels (thm : EMatchTheorem) : MetaM Expr := do
  Grind.getProofWithFreshMVarLevels thm

/--
Auxiliary function to expand a pattern containing forbidden application symbols
into a multi-pattern.

This function enhances the usability of the `[grind =]` attribute by automatically handling
forbidden pattern symbols. For example, consider the following theorem tagged with this attribute:
```
getLast?_eq_some_iff {xs : List α} {a : α} : xs.getLast? = some a ↔ ∃ ys, xs = ys ++ [a]
```
Here, the selected pattern is `xs.getLast? = some a`, but `Eq` is a forbidden pattern symbol.
Instead of producing an error, this function converts the pattern into a multi-pattern,
allowing the attribute to be used conveniently.

The function recursively expands patterns with forbidden symbols by splitting them
into their sub-components. If the pattern does not contain forbidden symbols,
it is returned as-is.
-/
partial def splitWhileForbidden (pat : Expr) : List Expr :=
  match_expr pat with
  | Not p => splitWhileForbidden p
  | And p₁ p₂ => splitWhileForbidden p₁ ++ splitWhileForbidden p₂
  | Or p₁ p₂ => splitWhileForbidden p₁ ++ splitWhileForbidden p₂
  | Eq _ lhs rhs => splitWhileForbidden lhs ++ splitWhileForbidden rhs
  | Iff lhs rhs => splitWhileForbidden lhs ++ splitWhileForbidden rhs
  | HEq _ lhs _ rhs => splitWhileForbidden lhs ++ splitWhileForbidden rhs
  | _ => [pat]

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
    return m!"_"
  else match pattern with
    | .bvar idx => return m!"#{idx}"
    | _ =>
      if pattern.isAppOfArity ``Grind.offset 2 then
        let lhs := ppArg <| pattern.getArg! 0
        let rhs := ppPattern <| pattern.getArg! 1
        return m!"{lhs} + {rhs}"
      else
        let mut r := m!"{pattern.getAppFn}"
        for arg in pattern.getAppArgs do
          r := r ++ " " ++ ppArg arg
        return r
where
  ppArg (arg : Expr) : MessageData :=
    if isAtomicPattern arg then
      ppPattern arg
    else
      .paren (ppPattern arg)

namespace NormalizePattern

structure State where
  symbols    : Array HeadIndex := #[]
  symbolSet  : Std.HashSet HeadIndex := {}
  bvarsFound : Std.HashSet Nat := {}

private structure Context where
  symPrios : SymbolPriorities
  /-- Only symbols with priority `>= minPrio` are considered in patterns. -/
  minPrio  : Nat

private abbrev M := ReaderT Context StateRefT State MetaM

private def isCandidateSymbol (declName : Name) (root : Bool) : M Bool := do
  let ctx ← read
  let prio := ctx.symPrios.getPrio declName
  -- Priority 0 are never considered, they are treated as forbidden
  if prio == 0 then return false
  -- If it is the root symbol, then we check whether `prio ≥ minPrio`
  if root then
    return prio ≥ ctx.minPrio
  else
    return true

private def saveSymbol (h : HeadIndex) : M Unit := do
  if let .const declName := h then
    if declName == ``Grind.genHEqPattern || declName == ``Grind.genPattern then
      -- We do not save gadgets in the list of symbols.
      return ()
  unless (← get).symbolSet.contains h do
    modify fun s => { s with symbols := s.symbols.push h, symbolSet := s.symbolSet.insert h }

private def saveSymbolsAt (e : Expr) : M Unit := do
  e.forEach' fun e => do
    if e.isApp || e.isConst then
      /- **Note**: We ignore function symbols that have special handling in the internalizer. -/
      if let .const declName _ := e.getAppFn then
        if declName == ``OfNat.ofNat || declName == ``Grind.nestedProof
           || declName == ``Grind.eqBwdPattern
           || declName == ``Grind.nestedDecidable || declName == ``ite then
          return false
    match e with
    | .const .. =>
      saveSymbol e.toHeadIndex
      return false
    | _ =>
      return true

private def foundBVar (idx : Nat) : M Bool :=
  return (← get).bvarsFound.contains idx

private def saveBVar (idx : Nat) : M Unit := do
  modify fun s => { s with bvarsFound := s.bvarsFound.insert idx }

inductive PatternArgKind where
  | /-- Argument is relevant for E-matching. -/
    relevant
  | /-- Instance implicit arguments are considered support and handled using `isDefEq`. -/
    instImplicit
  | /-- Proofs are ignored during E-matching. Lean is proof irrelevant. -/
    proof
  | /--
    Types and type formers are mostly ignored during E-matching, and processed using
    `isDefEq`. However, if the argument is of the form `C ..` where `C` is inductive type
    we process it as part of the pattern. Suppose we have `as bs : List α`, and a pattern
    candidate expression `as ++ bs`, i.e., `@HAppend.hAppend (List α) (List α) (List α) inst as bs`.
    If we completely ignore the types, the pattern will just be
    ```
    @HAppend.hAppend _ _ _ _ #1 #0
    ```
    This is not ideal because the E-matcher will try it in any goal that contains `++`,
    even if it does not even mention lists.
    -/
    typeFormer
    deriving Repr

def PatternArgKind.isSupport : PatternArgKind → Bool
  | .relevant => false
  | _ => true

/--
Returns an array `kinds` s.ts `kinds[i]` is the kind of the corresponding argument.

- a type (that is not a proposition) or type former (which has forward dependencies) or
- a proof, or
- an instance implicit argument

When `kinds[i].isSupport` is `true`, we say the corresponding argument is a "support" argument.
-/
def getPatternArgKinds (f : Expr) (numArgs : Nat) : MetaM (Array PatternArgKind) := do
  let pinfos := (← getFunInfoNArgs f numArgs).paramInfo
  forallBoundedTelescope (← inferType f) numArgs fun xs _ => do
    xs.mapIdxM fun idx x => do
      if (← isProp x) then
        return .relevant
      else if (← isProof x) then
        return .proof
      else if (← isTypeFormer x) then
        if h : idx < pinfos.size then
          /-
          We originally wanted to ignore types and type formers in `grind` and treat them as supporting elements.
          Thus, we wanted to always return `.typeFormer`. However, we changed our heuristic because of the following example:
          ```
          example {α} (f : α → Type) (a : α) (h : ∀ x, Nonempty (f x)) : Nonempty (f a) := by
            grind
          ```
          In this example, we are reasoning about types. Therefore, we adjusted the heuristic as follows:
          a type or type former is considered a supporting element only if it has forward dependencies.
          Note that this is not the case for `Nonempty`.
          -/
          if pinfos[idx].hasFwdDeps then return .typeFormer else return .relevant
        else
          return .typeFormer
      else
        let xDecl ← x.fvarId!.getDecl
        if xDecl.binderInfo matches .instImplicit then
          return .instImplicit
        /-
        **Note**: Even if the binder is not marked as instance implicit, we may still
        synthesize it using type class resolution. The motivation is declarations such as
        ```
        ZeroMemClass.zero_mem {S : Type} {M : outParam Type} {inst1 : Zero M} {inst2 : SetLike S M}
            [self : @ZeroMemClass S M inst1 inst2] (s : S) : 0 ∈ s
        ```
        Recall that a similar approach is used in `simp`.
        -/
        else if (← isClass? xDecl.type).isSome then
          return .instImplicit
        else
          return .relevant

private def getPatternFn? (pattern : Expr) (inSupport : Bool) (root : Bool) (argKind : PatternArgKind) : M (Option Expr) := do
  if !pattern.isApp && !pattern.isConst then
    return none
  else match pattern.getAppFn with
    | f@(.const declName _) =>
      if !(← isCandidateSymbol declName root) then
        return none
      if declName == ``Grind.genPattern || declName == ``Grind.genHEqPattern then
        return some f
      if inSupport then
        if argKind matches .typeFormer | .relevant then
          if (← isInductive declName) then
            return some f
        return none
      return some f
    | f@(.fvar _) =>
      if inSupport then return none else return some f
    | _ =>
      return none

/--
Helper type used during pattern normalization.
When normalizing a sub-pattern `p`, we store the kind of the parent pattern
using this enumeration type.
-/
private inductive ParentKind where
  | /-- No special treatment needed. -/
    regular
  | /--
    The parent pattern is the gadget `Grind.eqBwdPattern`.
    In this case, we do not collect the symbols in ground children pattern.
    -/
    eqBwdPattern
  | /--
    The parent pattern is the gadget `Grind.genPattern` and `Grind.genHEqPattern`.
    These gadgets assume the arguments are variables (see: `isGenPattern?`).
    Thus, during normalization we must not replace them with `dontCare`.
    -/
    genPattern

private def toParentKind (f : Expr) : ParentKind :=
  match f with
  | .const declName _ =>
    if declName == ``Grind.eqBwdPattern then
      .eqBwdPattern
    else if declName == ``Grind.genHEqPattern || declName == ``Grind.genPattern then
      .genPattern
    else
      .regular
  | _ => .regular

private partial def go (pattern : Expr) (inSupport : Bool) (root : Bool) : M Expr := do
  if let some (e, k) := isOffsetPattern? pattern then
    let e ← goArg e inSupport .relevant .regular
    if isPatternDontCare e then
      return dontCare
    else
      return mkOffsetPattern e k
  let some f ← getPatternFn? pattern inSupport root .relevant
    | throwError "invalid pattern, (non-forbidden) application expected{indentD (ppPattern pattern)}"
  assert! f.isConst || f.isFVar
  let parentKind := toParentKind f
  if parentKind matches .regular then
    saveSymbol f.toHeadIndex
  let mut args := pattern.getAppArgs.toVector
  let patternArgKinds ← getPatternArgKinds f args.size
  for h : i in *...args.size do
    let arg := args[i]
    let argKind := patternArgKinds[i]?.getD .relevant
    args := args.set i (← goArg arg (inSupport || argKind.isSupport) argKind parentKind)
  return mkAppN f args.toArray
where
  goArg (arg : Expr) (inSupport : Bool) (argKind : PatternArgKind) (parentKind : ParentKind) : M Expr := do
    if !arg.hasLooseBVars then
      if arg.hasMVar then
        pure dontCare
      else if (← isProof arg) then
        pure dontCare
      else
        let arg ← expandOffsetPatterns arg
        if !inSupport && parentKind matches .regular then
          /-
          **Note**: We ignore symbols in ground patterns if the parent is the auxiliary ``Grind.eqBwdPattern
          We do that because we want to sign an error in examples such as:
          ```
          theorem dummy (x : Nat) : x = x :=
            rfl
          -- error: invalid pattern for `dummy`
          --  [@Lean.Grind.eqBwdPattern `[Nat] #0 #0]
          -- the pattern does not contain constant symbols for indexing
          attribute [grind ←=] dummy
          ```
          -/
          saveSymbolsAt arg
        return mkGroundPattern arg
    else match arg with
      | .bvar idx =>
        -- **Note** See comment at `ParentKind.genPattern`.
        if inSupport && (← foundBVar idx) && !parentKind matches .genPattern then
          pure dontCare
        else
          saveBVar idx
          pure arg
      | _ =>
        if let some _ ← getPatternFn? arg inSupport (root := false) argKind then
          go arg inSupport (root := false)
        else
          pure dontCare

def main (patterns : List Expr) (symPrios : SymbolPriorities) (minPrio : Nat) : MetaM (List Expr × List HeadIndex × Std.HashSet Nat) := do
  let (patterns, s) ← patterns.mapM (go (inSupport := false) (root := true)) { symPrios, minPrio } |>.run {}
  return (patterns, s.symbols.toList, s.bvarsFound)

private def normalizePattern (e : Expr) : M Expr := do
  go e (inSupport := false) (root := true)

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
    let thmVars := FVarIdSet.ofList <| xs.toList.map (·.fvarId!)
    -- Collect free variables occurring in `e`, and insert the ones that are in `thmVars` into `fvarsFound`
    let update (fvarsFound : FVarIdSet) (e : Expr) : FVarIdSet :=
      (collectFVars {} e).fvarIds.foldl (init := fvarsFound) fun s fvarId =>
        if thmVars.contains fvarId then s.insert fvarId else s
    -- Theorem variables found so far. We initialize with the variables occurring in patterns
    -- Remark: fvarsFound is a subset of thmVars
    let mut fvarsFound := FVarIdSet.ofList patternVars
    for patternVar in patternVars do
      let type ← patternVar.getType
      fvarsFound := update fvarsFound type
    if fvarsFound.size == numParams then return .ok
    -- Now, we keep traversing remaining variables and collecting
    -- `processed` contains the variables we have already processed.
    let mut processed := FVarIdSet.ofList patternVars
    let mut modified := false
    repeat
      modified := false
      for x in xs do
        let fvarId := x.fvarId!
        unless processed.contains fvarId do
          let xDecl ← fvarId.getDecl
          let xType := xDecl.type
          if fvarsFound.contains fvarId then
            -- Collect free vars in `x`s type and mark as processed
            fvarsFound := update fvarsFound xType
            processed := processed.insert fvarId
            modified := true
          else
            /- **Note**: See comment at `getPatternArgKinds` -/
            let instImplicit ← if xDecl.binderInfo matches .instImplicit then
              pure true
            else
              pure <| (← isClass? xType).isSome
            if instImplicit then
              -- If `x` is instance implicit, check whether
              -- we have found all free variables needed to synthesize instance
              if (← canBeSynthesized thmVars fvarsFound xType) then
                fvarsFound := fvarsFound.insert fvarId
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
      if fvarsFound.size == numParams then
        return .ok
      if !modified then
        break
    let mut pos := #[]
    for h : i in *...xs.size do
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
    for h : i in *...xs.size do
      if paramPos.contains i then
        let x := xs[i]
        if first then first := false else msg := msg ++ "\n"
        msg := msg ++ m!"{x} : {← inferType x}"
    addMessageContextFull msg

private def logPatternWhen (showInfo : Bool) (origin : Origin) (patterns : List Expr) : MetaM Unit := do
  if showInfo then
    logInfo m!"{origin.pp}: {patterns.map ppPattern}"

/--
Creates an E-matching theorem for a theorem with proof `proof`, `numParams` parameters, and the given set of patterns.
Pattern variables are represented using de Bruijn indices.
-/
def mkEMatchTheoremCore (origin : Origin) (levelParams : Array Name) (numParams : Nat) (proof : Expr)
    (patterns : List Expr) (kind : EMatchTheoremKind) (cnstrs : List EMatchTheoremConstraint := []) (showInfo := false) (minIndexable : Bool := false) : MetaM EMatchTheorem := do
  -- the patterns have already been selected, there is no point in using priorities here
  let (patterns, symbols, bvarFound) ← NormalizePattern.main patterns (← getGlobalSymbolPriorities) (minPrio := 1)
  if symbols.isEmpty then
    throwError "invalid pattern for `{origin.pp}`{indentD (patterns.map ppPattern)}\nthe pattern does not contain constant symbols for indexing"
  trace[grind.ematch.pattern] "{origin.pp}: {patterns.map ppPattern}"
  if let .missing pos ← checkCoverage proof numParams bvarFound then
     let pats : MessageData := m!"{patterns.map ppPattern}"
     throwError "invalid pattern(s) for `{origin.pp}`{indentD pats}\nthe following theorem parameters cannot be instantiated:{indentD (← ppParamsAt proof numParams pos)}"
  logPatternWhen showInfo origin patterns
  return {
    proof, patterns, numParams, symbols
    levelParams, origin, kind, minIndexable, cnstrs
  }

private def getProofFor (declName : Name) : MetaM Expr := do
  let info ← getConstVal declName
  -- For theorems, `isProp` has already been checked at declaration time
  unless wasOriginallyTheorem (← getEnv) declName do
    unless (← isProp info.type) do
      throwError "invalid E-matching theorem `{.ofConstName declName}`, type is not a proposition"
  let us := info.levelParams.map mkLevelParam
  return mkConst declName us

/--
Creates an E-matching theorem for `declName` with `numParams` parameters, and the given set of patterns.
Pattern variables are represented using de Bruijn indices.
-/
def mkEMatchTheorem (declName : Name) (numParams : Nat) (patterns : List Expr)
    (kind : EMatchTheoremKind) (minIndexable : Bool) (cnstrs : List EMatchTheoremConstraint) : MetaM EMatchTheorem := do
  mkEMatchTheoremCore (.decl declName) #[] numParams (← getProofFor declName) patterns kind cnstrs (minIndexable := minIndexable)

/--
Given a theorem with proof `proof` and type of the form `∀ (a_1 ... a_n), lhs = rhs`,
creates an E-matching pattern for it using `addEMatchTheorem n [lhs]`
If `normalizePattern` is true, it applies the `grind` simplification theorems and simprocs to the pattern.
-/
def mkEMatchEqTheoremCore (origin : Origin) (levelParams : Array Name) (proof : Expr) (normalizePattern : Bool)
  (useLhs : Bool) (gen : Bool) (showInfo := false) : MetaM EMatchTheorem := do
  let (numParams, patterns) ← forallTelescopeReducing (← inferEMatchProofType proof gen) fun xs type => do
    let (lhs, rhs) ← match_expr type with
      | Eq _ lhs rhs => pure (lhs, rhs)
      | Iff lhs rhs => pure (lhs, rhs)
      | HEq _ lhs _ rhs => pure (lhs, rhs)
      | _ => throwError "invalid E-matching equality theorem, conclusion must be an equality{indentExpr type}"
    let pat := if useLhs then lhs else rhs
    trace[grind.debug.ematch.pattern] "mkEMatchEqTheoremCore: origin: {origin.pp}, pat: {pat}, useLhs: {useLhs}"
    let pat ← preprocessPattern pat normalizePattern
    trace[grind.debug.ematch.pattern] "mkEMatchEqTheoremCore: after preprocessing: {pat}, {← normalize pat normConfig}"
    let pats := splitWhileForbidden (pat.abstract xs)
    return (xs.size, pats)
  mkEMatchTheoremCore origin levelParams numParams proof patterns (if useLhs then .eqLhs gen else .eqRhs gen)
    (showInfo := showInfo) (minIndexable := false)

def mkEMatchEqBwdTheoremCore (origin : Origin) (levelParams : Array Name) (proof : Expr) (showInfo := false) : MetaM EMatchTheorem := do
  let (numParams, patterns) ← forallTelescopeReducing (← inferEMatchProofType proof (gen := false)) fun xs type => do
    let_expr f@Eq α lhs rhs := type
      | throwError "invalid E-matching `←=` theorem, conclusion must be an equality{indentExpr type}"
    let pat ← preprocessPattern (mkEqBwdPattern f.constLevels! α lhs rhs)
    return (xs.size, [pat.abstract xs])
  mkEMatchTheoremCore origin levelParams numParams proof patterns .eqBwd (showInfo := showInfo)
    (minIndexable := false)

def Extension.isEMatchTheorem (ext : Extension) (declName : Name) : CoreM Bool :=
  return ext.getState (← getEnv) |>.ematch.contains (.decl declName)

def Extension.getEMatchTheorems (ext : Extension) : CoreM EMatchTheorems := do
  return ext.getState (← getEnv) |>.ematch

-- **TODO**: Delete. We should use custom grind attributes for implementing the `lia` tactic.
/-- Returns the scoped E-matching theorems declared in the given namespace. -/
def Extension.getEMatchTheoremsForNamespace (ext : Extension) (namespaceName : Name) : CoreM (Array EMatchTheorem) := do
  let stateStack := ext.ext.getState (← getEnv)
  match stateStack.scopedEntries.map.find? namespaceName with
  | none => return #[]
  | some entries => return entries.toArray.filterMap fun
    | .ematch thm => some thm
    | _ => none

/--
Given theorem with name `declName` and type of the form `∀ (a_1 ... a_n), lhs = rhs`,
creates an E-matching pattern for it using `addEMatchTheorem n [lhs]`

If `normalizePattern` is true, it applies the `grind` simplification theorems and simprocs to the
pattern.
-/
def mkEMatchEqTheorem (declName : Name) (normalizePattern := true) (useLhs : Bool := true) (gen : Bool := false) (showInfo := false) : MetaM EMatchTheorem := do
  mkEMatchEqTheoremCore (.decl declName) #[] (← getProofFor declName) normalizePattern useLhs gen (showInfo := showInfo)

/--
Adds an E-matching theorem to the environment.
See `mkEMatchTheorem`.
-/
def Extension.addEMatchTheorem (ext : Extension) (declName : Name) (numParams : Nat) (patterns : List Expr) (kind : EMatchTheoremKind)
    (minIndexable : Bool) (attrKind := AttributeKind.global) (cnstrs : List EMatchTheoremConstraint) : MetaM Unit := do
  ext.add (.ematch (← mkEMatchTheorem declName numParams patterns kind cnstrs (minIndexable := minIndexable))) attrKind

/--
Adds an E-matching equality theorem to the environment.
See `mkEMatchEqTheorem`.
-/
def Extension.addEMatchEqTheorem (ext : Extension) (declName : Name) : MetaM Unit := do
  ext.add (.ematch (← mkEMatchEqTheorem declName))

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
  | .const declName _ => NormalizePattern.isCandidateSymbol declName (root := true)
  | .fvar .. => return !(← read).xs.contains f
  | _ => return false

private def addNewPattern (p : Expr) : CollectorM Unit := do
  trace[grind.debug.ematch.pattern] "found pattern: {ppPattern p}"
  let bvarsFound := (← getThe NormalizePattern.State).bvarsFound
  let done := (← checkCoverage (← read).proof (← read).xs.size bvarsFound) matches .ok
  if done then
    trace[grind.debug.ematch.pattern] "found full coverage"
  modify fun s => { s with patterns := s.patterns.push p, done }

/-- Collect the pattern (i.e., de Bruijn) variables in the given pattern. -/
private def collectPatternBVars (p : Expr) : List Nat :=
  go p |>.run [] |>.2
where
  go (e : Expr) : StateM (List Nat) Unit := do
    match e with
    | .app f a    => go f; go a
    | .mdata _ b  => go b
    | .bvar idx   => modify fun s => if s.contains idx then s else idx :: s
    | _           => return ()

namespace OldCollector
private def diff (s : List Nat) (found : Std.HashSet Nat) : List Nat :=
  if found.isEmpty then s else s.filter fun x => !found.contains x

/--
Returns `true` if pattern `p` contains a child `c` such that
1- `p` and `c` have the same new pattern variables. We say a pattern variable is new if it is not in `alreadyFound`.
2- `c` is not a support argument. See `NormalizePattern.getPatternSupportMask` for definition.
3- `c` is not an offset pattern.
4- `c` is not a bound variable.
-/
private def hasChildWithSameNewBVars (p : Expr)
    (argKinds : Array NormalizePattern.PatternArgKind) (alreadyFound : Std.HashSet Nat) : CoreM Bool := do
  let s := diff (collectPatternBVars p) alreadyFound
  for arg in p.getAppArgs, argKind in argKinds do
    unless argKind.isSupport do
    unless arg.isBVar do
    unless isOffsetPattern? arg |>.isSome do
      let sArg := diff (collectPatternBVars arg) alreadyFound
      if s ⊆ sArg then
        return true
  return false

private partial def collect (e : Expr) : CollectorM Unit := do
  if (← get).done then return ()
  match e with
  | .app .. =>
    trace[grind.debug.ematch.pattern] "collect: {e}"
    let f := e.getAppFn
    let argKinds ← NormalizePattern.getPatternArgKinds f e.getAppNumArgs
    if (← isPatternFnCandidate f) then
      let saved ← getThe NormalizePattern.State
      try
        trace[grind.debug.ematch.pattern] "candidate: {e}"
        let p := e.abstract (← read).xs
        unless p.hasLooseBVars do
          trace[grind.debug.ematch.pattern] "skip, does not contain pattern variables"
          return ()
        let p ← NormalizePattern.normalizePattern p
        if saved.bvarsFound.size < (← getThe NormalizePattern.State).bvarsFound.size then
          unless (← hasChildWithSameNewBVars p argKinds saved.bvarsFound) do
            addNewPattern p
            return ()
        trace[grind.debug.ematch.pattern] "skip, no new variables covered"
        -- restore state and continue search
        set saved
      catch ex =>
        trace[grind.debug.ematch.pattern] "skip, exception during normalization{indentD ex.toMessageData}"
        -- restore state and continue search
        set saved
    let args := e.getAppArgs
    for arg in args, argKind in argKinds do
      trace[grind.debug.ematch.pattern] "arg: {arg}, support: {argKind.isSupport}"
      unless argKind.isSupport do
        collect arg
  | .forallE _ d b _ =>
    if (← pure e.isArrow <&&> isProp d <&&> isProp b) then
      collect d
      collect b
  | _ => return ()

end OldCollector

private def sizeOfDiff (s₁ s₂ : Std.HashSet Nat) : Nat :=
  s₂.fold (init := s₁.size) fun num idx =>
    if s₁.contains idx then num - 1 else num

/--
Normalizes `e` if it qualifies as a candidate pattern, and returns
`some p` where `p` is the normalized pattern.

`argKinds == NormalizePattern.getPatternArgKinds e.getAppFn e.getAppNumArgs`

If `minIndexable == true`, then enforces the minimal indexable subexpression condition.
That is, an indexable subexpression is minimal if there is no smaller indexable subexpression
whose head constant has at least as high priority.
-/
private def normalizePattern? (e : Expr) (argKinds : Array NormalizePattern.PatternArgKind)
    (minIndexable : Bool) : CollectorM (Option Expr) := do
  let p := e.abstract (← read).xs
  unless p.hasLooseBVars do
    trace[grind.debug.ematch.pattern] "skip, does not contain pattern variables"
    return none
  -- Normalization state before normalizing `e`
  let stateBefore ← getThe NormalizePattern.State
  let failed : CollectorM (Option Expr) := do
    set stateBefore
    return none
  -- Returns the number of new variables with respect to `saved`
  let getNumNewBVars : NormalizePattern.M Nat := do
    return sizeOfDiff (← get).bvarsFound stateBefore.bvarsFound
  try
    let p ← NormalizePattern.normalizePattern p
    let numNewBVars ← getNumNewBVars
    if numNewBVars == 0 then
      trace[grind.debug.ematch.pattern] "skip, no new variables covered"
      return (← failed)
    if minIndexable then
      let stateAfter ← getThe NormalizePattern.State
      /-
      Checks whether one of `e`s children subsumes it. We say a child `c` subsumes `e`
      1- `e` and `c` have the same new pattern variables. We say a pattern variable is new if it is not in `stateOld.bvarsFound`.
      2- `c` is not a support argument. See `NormalizePattern.getPatternSupportMask` for definition.
      3- `c` is not an offset pattern.
      4- `c` is not a bound variable.
      5- `c` is also a candidate.
      -/
      for arg in e.getAppArgs, argKind in argKinds do
        unless argKind.isSupport do
        unless arg.isFVar do
        unless isOffsetPattern? arg |>.isSome do
        if (← isPatternFnCandidate arg.getAppFn) then
          let pArg := arg.abstract (← read).xs
          set stateBefore
          discard <|  NormalizePattern.normalizePattern pArg
          let numArgNewBVars ← getNumNewBVars
          if numArgNewBVars == numNewBVars then
            trace[grind.debug.ematch.pattern] "skip, subsumed by argument"
            return (← failed)
      set stateAfter
    return some p
  catch ex =>
    trace[grind.debug.ematch.pattern] "skip, exception during normalization{indentD ex.toMessageData}"
    failed

private partial def collect (e : Expr) (minIndexable : Bool) : CollectorM Unit := do
  go e
where
  go (e : Expr) : CollectorM Unit := do
    if (← get).done then return ()
    match e with
    | .app .. =>
      trace[grind.debug.ematch.pattern] "collect: {e}"
      let f := e.getAppFn
      let argKinds ← NormalizePattern.getPatternArgKinds f e.getAppNumArgs
      if (← isPatternFnCandidate f) then
        trace[grind.debug.ematch.pattern] "candidate: {e}"
        if let some p ← normalizePattern? e argKinds minIndexable then
          addNewPattern p
          return ()
      let args := e.getAppArgs
      for arg in args, argKind in argKinds do
        unless isOffsetPattern? arg |>.isSome do
        trace[grind.debug.ematch.pattern] "arg: {arg}, support: {argKind.isSupport}"
        unless argKind.isSupport do
          go arg
    | .forallE _ d b _ =>
      if (← pure e.isArrow <&&> isProp d <&&> isProp b) then
        go d
        go b
    | _ => return ()

register_builtin_option backward.grind.inferPattern : Bool := {
  defValue := false
  descr    := "use old E-matching pattern inference"
}

register_builtin_option backward.grind.checkInferPatternDiscrepancy : Bool := {
  defValue := false
  descr    := "check whether old and new pattern inference procedures infer the same pattern"
}

private def collectPatterns? (proof : Expr) (xs : Array Expr) (searchPlaces : Array Expr) (symPrios : SymbolPriorities) (minPrio : Nat)
    (minIndexable : Bool) : MetaM (Option (List Expr × List HeadIndex)) := do
  let go (useOld : Bool): CollectorM (Option (List Expr)) := do
    for place in searchPlaces do
      trace[grind.debug.ematch.pattern] "place: {place}"
      let place ← preprocessPattern place
      if useOld then
        OldCollector.collect place
      else
        collect place minIndexable
      if (← get).done then
        return some ((← get).patterns.toList)
    return none
  let collect? (useOld : Bool) : MetaM (Option (List Expr × List HeadIndex)) := do
    let (some ps, s) ← go useOld { proof, xs } |>.run' {} { symPrios, minPrio } |>.run {}
      | return none
    return some (ps, s.symbols.toList)
  let useOld := backward.grind.inferPattern.get (← getOptions)
  if backward.grind.checkInferPatternDiscrepancy.get (← getOptions) then
    let oldResult? ← collect? (useOld := true)
    let newResult? ← collect? (useOld := false)
    let toPattern (result? : Option (List Expr × List HeadIndex)) : List MessageData :=
      let pat := result?.map (·.1) |>.getD []
      pat.map ppPattern
    if oldResult? != newResult? then
      logWarning m!"found discrepancy between old and new `grind` pattern inference procedures, old:{indentD (toPattern oldResult?)}\nnew:{indentD (toPattern newResult?)}"
    return if useOld then oldResult? else newResult?
  else
    collect? useOld

/--
Tries to find a ground pattern to activate the theorem.
This is used for theorems such as `theorem evenZ : Even 0`.
This function is only used if `collectPatterns?` returns `none`.

Remark: only symbols with priority `>= minPrio` are considered.
-/
private partial def collectGroundPattern? (proof : Expr) (xs : Array Expr) (searchPlaces : Array Expr) (symPrios: SymbolPriorities) (minPrio : Nat)
    : MetaM (Option (Expr × List HeadIndex)) := do
  unless (← checkCoverage proof xs.size {}) matches .ok do
    return none
  let go? : CollectorM (Option Expr) := do
    for place in searchPlaces do
      let place ← preprocessPattern place
      if let some r ← visit? place then
        return r
    return none
  let (some p, s) ← go? { proof, xs } |>.run' {} { symPrios, minPrio } |>.run {}
    | return none
  return some (p, s.symbols.toList)
where
  visit? (e : Expr) : CollectorM (Option Expr) := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      if (← isPatternFnCandidate f) then
        let e ← NormalizePattern.normalizePattern e
        return some e
      else
        let args := e.getAppArgs
        for arg in args, argKind in (← NormalizePattern.getPatternArgKinds f args.size) do
          unless argKind.isSupport do
            if let some r ← visit? arg then
              return r
        return none
    | .forallE _ d b _ =>
      if (← pure e.isArrow <&&> isProp d <&&> isProp b) then
        if let some d ← visit? d then return d
        visit? b
      else
        return none
    | _ => return none

def EMatchTheoremKind.gen : EMatchTheoremKind → Bool
  | .eqLhs gen => gen
  | .eqRhs gen => gen
  | .eqBoth gen => gen
  | .default gen => gen
  | .bwd gen => gen
  | .eqBwd | .fwd | .rightLeft
  | .leftRight | .user => false

private def collectUsedPriorities (prios : SymbolPriorities) (searchPlaces : Array Expr) : Array Nat := Id.run do
  let mut s : Std.HashSet Nat := {}
  for place in searchPlaces do
    s := place.foldConsts (init := s) fun declName s =>
      let prio := prios.getPrio declName
      if prio > 0 then s.insert prio else s
  let r := s.toArray
  if r.isEmpty then
    return #[eval_prio default]
  else
    return r.qsort fun p₁ p₂ => p₁ > p₂

/-- Helper function for collecting all singleton patterns. -/
private partial def collectSingletons (e : Expr) : StateT (Array (Expr × List HeadIndex)) CollectorM Unit := do
  match e with
  | .app .. =>
    trace[grind.debug.ematch.pattern] "collect: {e}"
    let f := e.getAppFn
    let argKinds ← NormalizePattern.getPatternArgKinds f e.getAppNumArgs
    if (← isPatternFnCandidate f) then
      -- Reset collector and normalizer states. Recall that we are collecting singleton patterns only.
      set { : NormalizePattern.State }
      set { : Collector.State }
      try
        trace[grind.debug.ematch.pattern] "candidate: {e}"
        let p := e.abstract (← read).xs
        unless p.hasLooseBVars do
          trace[grind.debug.ematch.pattern] "skip, does not contain pattern variables"
          return ()
        -- **TODO**: `minIndexable` support
        let p ← NormalizePattern.normalizePattern p
        addNewPattern p
        if (← getThe Collector.State).done then
          let p := (← getThe Collector.State).patterns.back!
          let idxs := (← getThe NormalizePattern.State).symbols
          if (← get).all fun (p', _) => p != p' then
            modify fun s => s.push (p, idxs.toList)
      catch ex =>
        trace[grind.debug.ematch.pattern] "skip, exception during normalization{indentD ex.toMessageData}"
    let args := e.getAppArgs
    for arg in args, argKind in argKinds do
      trace[grind.debug.ematch.pattern] "arg: {arg}, support: {argKind.isSupport}"
      unless argKind.isSupport do
        collectSingletons arg
  | .forallE _ d b _ =>
    if (← pure e.isArrow <&&> isProp d <&&> isProp b) then
      collectSingletons d
      collectSingletons b
  | _ => return ()

/--
Collects all singleton patterns in the type of the given proof.
We use this function to implement local forall expressions in a `grind` goal.
-/
def mkEMatchTheoremUsingSingletonPatterns (origin : Origin) (levelParams : Array Name) (proof : Expr) (minPrio : Nat) (symPrios : SymbolPriorities)
    (showInfo := false) : MetaM (Array EMatchTheorem) := do
  let type ← inferEMatchProofType proof (gen := false)
  withReducible <| forallTelescopeReducing type fun xs type => withDefault do
    let (_, s) ← go xs type |>.run {} |>.run { proof, xs } |>.run' {} { symPrios, minPrio } |>.run' {}
    let numParams := xs.size
    let mut thms := #[]
    for (p, symbols) in s do
      let patterns := [p]
      logPatternWhen showInfo origin patterns
      let thm : EMatchTheorem := {
        proof, patterns, numParams, symbols,
        levelParams, origin, kind := .default false
        minIndexable := false
      }
      thms := thms.push thm
    return thms
where
  go (xs : Array Expr) (type : Expr) : StateT (Array (Expr × List HeadIndex)) CollectorM Unit := do
    for x in xs do
      collectSingletons (← inferType x)
    collectSingletons type

/--
Creates an E-match theorem using the given proof and kind.
If `groundPatterns` is `true`, it accepts patterns without pattern variables. This is useful for
theorems such as `theorem evenZ : Even 0`. For local theorems, we use `groundPatterns := false`
since the theorem is already in the `grind` state and there is nothing to be instantiated.
-/
def mkEMatchTheoremWithKind?
      (origin : Origin) (levelParams : Array Name) (proof : Expr) (kind : EMatchTheoremKind) (symPrios : SymbolPriorities)
      (groundPatterns := true) (showInfo := false) (minIndexable := false) : MetaM (Option EMatchTheorem) := do
  match kind with
  | .eqLhs gen =>
    return (← mkEMatchEqTheoremCore origin levelParams proof (normalizePattern := true) (useLhs := true) (gen := gen) (showInfo := showInfo))
  | .eqRhs gen =>
    return (← mkEMatchEqTheoremCore origin levelParams proof (normalizePattern := true) (useLhs := false) (gen := gen) (showInfo := showInfo))
  | .eqBwd =>
    return (← mkEMatchEqBwdTheoremCore origin levelParams proof (showInfo := showInfo))
  | _ =>
    pure ()
  let type ← inferEMatchProofType proof kind.gen
  /-
  Remark: we should not use `forallTelescopeReducing` (with default reducibility) here
  because it may unfold a definition/abstraction, and then select a suboptimal pattern.
  Here is an example. Suppose we have
  ```
  def State.le (σ₁ σ₂ : State) : Prop := ∀ ⦃x : Var⦄ ⦃v : Val⦄, σ₁.find? x = some v → σ₂.find? x = some v

  infix:50 " ≼ " => State.le
  ```
  Then, we write the theorem
  ```
  @[grind] theorem State.join_le_left (σ₁ σ₂ : State) : σ₁.join σ₂ ≼ σ₁ := by
  ```
  We do not want `State.le` to be unfolded and the abstraction exposed.

  That said, we must still reduce `[reducible]` definitions since `grind` unfolds them.
  -/
  withReducible <| forallTelescopeReducing type fun xs type => withDefault do
    let searchPlaces ← match kind with
      | .fwd =>
        let ps ← getPropTypes xs
        if ps.isEmpty then
          throwError "invalid `grind` forward theorem, theorem `{origin.pp}` does not have propositional hypotheses"
        pure ps
      | .bwd _ => pure #[type]
      | .leftRight => pure <| (← getPropTypes xs).push type
      | .rightLeft => pure <| #[type] ++ (← getPropTypes xs).reverse
      | .default _ => pure <| #[type] ++ (← getPropTypes xs)
      | _ => unreachable!
    go xs searchPlaces
where
  collect (xs : Array Expr) (searchPlaces : Array Expr) : MetaM (Option (List Expr × List HeadIndex)) := do
    let prios := collectUsedPriorities symPrios searchPlaces
    for minPrio in prios do
      if let some r ← collectPatterns? proof xs searchPlaces symPrios minPrio (minIndexable := minIndexable) then
        return some r
      else if groundPatterns then
        if let some (pattern, symbols) ← collectGroundPattern? proof xs searchPlaces symPrios minPrio then
          return some ([pattern], symbols)
    return none

  go (xs : Array Expr) (searchPlaces : Array Expr) : MetaM (Option EMatchTheorem) := do
    let some (patterns, symbols) ← collect xs searchPlaces | return none
    let numParams := xs.size
    trace[grind.ematch.pattern] "{origin.pp}: {patterns.map ppPattern}"
    logPatternWhen showInfo origin patterns
    return some {
      proof, patterns, numParams, symbols
      levelParams, origin, kind, minIndexable
    }

def mkEMatchTheoremForDecl (declName : Name) (thmKind : EMatchTheoremKind) (prios : SymbolPriorities)
    (showInfo := false) (minIndexable := false) : MetaM EMatchTheorem := do
  let some thm ← mkEMatchTheoremWithKind? (.decl declName) #[] (← getProofFor declName) thmKind prios (showInfo := showInfo) (minIndexable := minIndexable)
    | throwError "`@{thmKind.toAttribute minIndexable} theorem {.ofConstName declName}` {thmKind.explainFailure}, consider using different options or the `grind_pattern` command"
  return thm

def mkEMatchEqTheoremsForDef? (declName : Name) (showInfo := false) : MetaM (Option (Array EMatchTheorem)) := do
  let some eqns ← getEqnsFor? declName | return none
  eqns.mapM fun eqn => do
    mkEMatchEqTheorem eqn (normalizePattern := true) (showInfo := showInfo)

private def Extension.addGrindEqAttr (ext : Extension) (declName : Name) (attrKind : AttributeKind) (thmKind : EMatchTheoremKind) (useLhs := true) (showInfo := false) : MetaM Unit := do
  if wasOriginallyTheorem (← getEnv) declName then
    ext.add (.ematch (← mkEMatchEqTheorem declName (normalizePattern := true) (useLhs := useLhs) (gen := thmKind.gen) (showInfo := showInfo))) attrKind
  else if let some thms ← mkEMatchEqTheoremsForDef? declName (showInfo := showInfo) then
    unless useLhs do
      throwError "`{.ofConstName declName}` is a definition, you must only use the left-hand side for extracting patterns"
    thms.forM fun thm => ext.add (.ematch thm) attrKind
  else
    throwError s!"`{thmKind.toAttribute false}` attribute can only be applied to equational theorems or function definitions"

def EMatchTheorems.eraseDecl (s : EMatchTheorems) (declName : Name) : MetaM EMatchTheorems := do
  if !wasOriginallyTheorem (← getEnv) declName then
    if let some eqns ← getEqnsFor? declName then
       unless eqns.all fun eqn => s.contains (.decl eqn) do
         throwNotMarkedWithGrindAttribute declName
       return eqns.foldl (init := s) fun s eqn => s.erase (.decl eqn)
    else
      throwNotMarkedWithGrindAttribute declName
  else
    unless s.contains (.decl declName) do
      throwNotMarkedWithGrindAttribute declName
    return s.erase <| .decl declName

private def ensureNoMinIndexable (minIndexable : Bool) : MetaM Unit := do
  if minIndexable then
    throwError "redundant modifier `!` in `grind` attribute"

def Extension.addEMatchAttr (ext : Extension) (declName : Name) (attrKind : AttributeKind) (thmKind : EMatchTheoremKind) (prios : SymbolPriorities)
    (showInfo := false) (minIndexable := false) : MetaM Unit := do
  match thmKind with
  | .eqLhs _ =>
    ensureNoMinIndexable minIndexable
    ext.addGrindEqAttr declName attrKind thmKind (useLhs := true) (showInfo := showInfo)
  | .eqRhs _ =>
    ensureNoMinIndexable minIndexable
    ext.addGrindEqAttr declName attrKind thmKind (useLhs := false) (showInfo := showInfo)
  | .eqBoth _ =>
    ensureNoMinIndexable minIndexable
    ext.addGrindEqAttr declName attrKind thmKind (useLhs := true) (showInfo := showInfo)
    ext.addGrindEqAttr declName attrKind thmKind (useLhs := false) (showInfo := showInfo)
  | _ =>
    let info ← getConstInfo declName
    if !wasOriginallyTheorem (← getEnv) declName && !info.isCtor && !info.isAxiom then
      ensureNoMinIndexable minIndexable
      ext.addGrindEqAttr declName attrKind thmKind (showInfo := showInfo)
    else
      let thm ← mkEMatchTheoremForDecl declName thmKind prios (showInfo := showInfo) (minIndexable := minIndexable)
      ext.add (.ematch thm) attrKind

private structure SelectM.State where
  -- **Note**: hack, an attribute is not a tactic.
  suggestions : Array Tactic.TryThis.Suggestion := #[]
  thms : Array EMatchTheorem := #[]

private abbrev SelectM := StateT SelectM.State MetaM

def EMatchTheoremKind.toSyntax (kind : EMatchTheoremKind) : CoreM (TSyntax ``Parser.Attr.grindMod) :=
  match kind with
  | .eqLhs true     => `(Parser.Attr.grindMod| = gen)
  | .eqLhs false    => `(Parser.Attr.grindMod|=)
  | .eqRhs true     => `(Parser.Attr.grindMod|=_ gen)
  | .eqRhs false    => `(Parser.Attr.grindMod|=_)
  | .eqBoth false   => `(Parser.Attr.grindMod|_=_)
  | .eqBoth true    => `(Parser.Attr.grindMod|_=_ gen)
  | .eqBwd          => `(Parser.Attr.grindMod|←=)
  | .fwd            => `(Parser.Attr.grindMod|→)
  | .bwd false      => `(Parser.Attr.grindMod|←)
  | .bwd true       => `(Parser.Attr.grindMod|← gen)
  | .leftRight      => `(Parser.Attr.grindMod|=>)
  | .rightLeft      => `(Parser.Attr.grindMod|<=)
  | .default false  => `(Parser.Attr.grindMod|.)
  | .default true   => `(Parser.Attr.grindMod|. gen)
  | .user           => throwError "`grind` theorem kind is not a modifier"

private def save (ref : Syntax) (thm : EMatchTheorem) (isParam : Bool) (minIndexable : Bool) : SelectM Unit := do
  -- We only save `thm` if the pattern is different from the ones that were already found.
  if (← get).thms.all fun thm' => thm.patterns != thm'.patterns then
    let pats ← thm.patterns.mapM fun p => do
      let pats ← addMessageContextFull (ppPattern p)
      -- **Note**: Add function for adding naming context, or store `MessageData` directly in the suggestion.
      let currNamespace ← getCurrNamespace
      let openDecls ← getOpenDecls
      let pats := MessageData.withNamingContext {currNamespace, openDecls} pats
      pats.format
    let openBracket  := if isParam then "" else "["
    let closeBracket := if isParam then "" else "]"
    let msg := s!"{closeBracket} for pattern: {pats}"
    let suggestion : Tactic.TryThis.SuggestionText ← match isParam, minIndexable with
      | false, true  => pure <| Tactic.TryThis.SuggestionText.tsyntax (← `(attr|grind! $(← thm.kind.toSyntax)))
      | false, false => pure <| .tsyntax (← `(attr|grind $(← thm.kind.toSyntax)))
      | true,  true  => pure <| .tsyntax (← `(Parser.Tactic.grindParam|!$(← thm.kind.toSyntax)$(⟨ref⟩):ident))
      | true, false  => pure <| .tsyntax (← `(Parser.Tactic.grindParam|$(← thm.kind.toSyntax) $(⟨ref⟩):ident))
    modify fun s => { s with
      thms := s.thms.push thm
      suggestions := s.suggestions.push {
        suggestion
        -- **Note**: small hack to include brackets in the suggestion
        preInfo?   := some openBracket
        -- **Note**: appears only in the info view.
        postInfo?  := some msg
      }
    }

register_builtin_option grind.param.codeAction : Bool := {
  defValue := false
  descr    := "code-action for `grind` parameters"
}

/-- Helper type for generating suggestions for `grind` parameters -/
inductive MinIndexableMode where
  | /-- `minIndexable := true` -/
    yes
  | /-- `minIndexable := false` -/
    no
  | /--
    Tries with and without the minimal indexable subexpression condition, if both produce the
    same pattern, use the one `minIndexable := false` since it is more compact.
    -/
    both

/--
Tries different modifiers, logs info messages with modifiers that worked, but returns just the first one that worked.
-/
def mkEMatchTheoremAndSuggest (ref : Syntax) (declName : Name) (prios : SymbolPriorities)
    (minIndexable : Bool) (isParam : Bool := false) : MetaM EMatchTheorem := do
  let tryModifier (thmKind : EMatchTheoremKind) (minIndexable : MinIndexableMode) : SelectM Unit := do
    try
      match minIndexable with
      | .yes =>
        let thm ← mkEMatchTheoremForDecl declName thmKind prios (showInfo := false) (minIndexable := true)
        save ref thm (minIndexable := true) (isParam := isParam)
      | .no =>
        let thm ← mkEMatchTheoremForDecl declName thmKind prios (showInfo := false) (minIndexable := false)
        save ref thm (minIndexable := false) (isParam := isParam)
      | .both =>
        let thm₁ ← mkEMatchTheoremForDecl declName thmKind prios (showInfo := false) (minIndexable := true)
        let thm₂ ← mkEMatchTheoremForDecl declName thmKind prios (showInfo := false) (minIndexable := false)
        if thm₁.patterns == thm₂.patterns then
          -- If both produce the same pattern, we save only `minIndexable := false` since it is more compact
          save ref thm₂ (minIndexable := false) (isParam := isParam)
        else
          save ref thm₁ (minIndexable := true) (isParam := isParam)
          save ref thm₂ (minIndexable := false) (isParam := isParam)
    catch _ =>
      return ()
  let searchCore (minIndexable : MinIndexableMode) : SelectM Unit := do
    tryModifier (.default false) minIndexable
    tryModifier (.bwd false) minIndexable
    tryModifier .fwd minIndexable
    tryModifier .rightLeft minIndexable
    tryModifier .leftRight minIndexable
  let search : SelectM Unit := do
    if minIndexable then
      searchCore .yes
    else if isParam then
      searchCore .both
      tryModifier (.eqLhs false) .no
      tryModifier (.eqRhs false) .no
    else
      tryModifier (.eqLhs false) .no
      tryModifier (.eqRhs false) .no
      searchCore .no
      searchCore .yes
  let (_, s) ← search.run {}
  if h₁ : 0 < s.thms.size then
    if !isParam || grind.param.codeAction.get (← getOptions) then
      if s.suggestions.size == 1 then
        Tactic.TryThis.addSuggestion ref s.suggestions[0]!
      else
        Tactic.TryThis.addSuggestions ref s.suggestions
    return s.thms[0]
  else
    throwError "invalid `grind` theorem, failed to find an usable pattern using different modifiers"

/--
Tries different modifiers, logs info messages with modifiers that worked, but stores just the first one that worked.

Remark: if `backward.grind.inferPattern` is `true`, then `.default false` is used.
The parameter `showInfo` is only taken into account when `backward.grind.inferPattern` is `true`.
-/
def Extension.addEMatchAttrAndSuggest (ext : Extension) (ref : Syntax) (declName : Name) (attrKind : AttributeKind) (prios : SymbolPriorities)
    (minIndexable : Bool) (showInfo : Bool) (isParam : Bool := false) : MetaM Unit := do
  let info ← getConstInfo declName
  if !wasOriginallyTheorem (← getEnv) declName && !info.isCtor && !info.isAxiom then
    ensureNoMinIndexable minIndexable
    ext.addGrindEqAttr declName attrKind (.default false) (showInfo := showInfo)
  else if backward.grind.inferPattern.get (← getOptions) then
    ext.addEMatchAttr declName attrKind (.default false) prios (minIndexable := minIndexable) (showInfo := showInfo)
  else
    let thm ← mkEMatchTheoremAndSuggest ref declName prios minIndexable isParam
    ext.add (.ematch thm) attrKind

end Lean.Meta.Grind
