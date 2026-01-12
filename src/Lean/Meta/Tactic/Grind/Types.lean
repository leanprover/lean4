/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Tactic.Simp.Types
public import Lean.Meta.Tactic.Grind.Attr
public import Lean.Meta.Tactic.Grind.CheckResult
public import Lean.Meta.Tactic.Grind.Extension
public import Init.Data.Queue
import Lean.HeadIndex
import Lean.Meta.Tactic.Grind.ExtAttr
import Lean.Meta.AbstractNestedProofs
import Lean.Meta.Match.MatchEqsExt
import Lean.PrettyPrinter
meta import Lean.Parser.Do
public section
namespace Lean.Meta.Grind
export Sym (isSameExpr hashPtrExpr ExprPtr shareCommon shareCommonInc)

/-- We use this auxiliary constant to mark delayed congruence proofs. -/
def congrPlaceholderProof := mkConst (Name.mkSimple "[congruence]")

/--
We use this auxiliary constant to mark delayed symmetric congruence proofs.
**Example:** `a = b` is symmetrically congruent to `c = d` if `a = d` and `b = c`.

**Note:** We previously used `congrPlaceholderProof` for this case, but it
caused non-termination during proof term construction when `a = b = c = d`.
The issue was that we did not have enough information to determine how
`a = b` and `c = d` became congruent. The new marker resolves this issue.

If `congrPlaceholderProof` is used, then `a = b` became congruent to `c = d`
because `a = c` and `b = d`.
If `eqCongrSymmPlaceholderProof` is used, then it was because `a = d` and `b = c`.

**Example:** suppose we have the following equivalence class:
```
{p, q, p = q, q = p, True}
```
Recall that `True` is always the root of its equivalence class.
Assume we also have the following two paths in the class:
```
1. p -> p = q -> q = p -> True
2. q -> True
```
Now suppose we try to build a proof for `p = True`.
We must construct a proof for `(p = q) = (q = p)`.
These equalities are congruent, but if we try to prove `p = q` and `q = p`
using the facts `p = True` and `q = True`, we end up trying to prove `p = True` again.
In other words, we are missing the information that `p = q` became congruent to `q = p`
because of the symmetric case. By using `eqCongrSymmPlaceholderProof`, we retain this information.
-/
def eqCongrSymmPlaceholderProof := mkConst (Name.mkSimple "[eq_congr_symm]")

/--
Returns `true` if `e` is `True`, `False`, or a literal value.
See `Lean.Meta.LitValues` for supported literals.
-/
def isInterpreted (e : Expr) : MetaM Bool := do
  if e.isTrue || e.isFalse then return true
  isLitValue e

register_builtin_option grind.debug : Bool := {
  defValue := false
  descr    := "check invariants after updates"
}

register_builtin_option grind.debug.proofs : Bool := {
  defValue := false
  descr    := "check proofs between the elements of all equivalence classes"
}

register_builtin_option grind.warning : Bool := {
  defValue := false
  descr    := "generate a warning whenever `grind` is used"
}

/--
Anchors are used to reference terms, local theorems, and case-splits in the `grind` state.
We also use anchors to prune the search space when they are provided as `grind` parameters
and the `finish` tactic.
-/
structure AnchorRef where
  numDigits : Nat
  anchorPrefix : UInt64

/-- Opaque solver extension state. -/
opaque SolverExtensionStateSpec : (α : Type) × Inhabited α := ⟨Unit, ⟨()⟩⟩
@[expose] def SolverExtensionState : Type := SolverExtensionStateSpec.fst
instance : Inhabited SolverExtensionState := SolverExtensionStateSpec.snd

/--
Case-split source. That is, where it came from.
We store the current source in the `grind` context.
-/
inductive SplitSource where
  | /-- Generated while instantiating a theorem using E-matching. -/
    ematch (origin : Origin)
  | /-- Generated while instantiating an extensionality theorem with name `declName` -/
    ext (declName : Name)
  | /-- Model-based theory combination equality coming from the i-th argument of applications `a` and `b` -/
    mbtc (a b : Expr) (i : Nat)
  | /-- Beta-reduction. -/
    beta (e : Expr)
  | /-- Forall-propagator. -/
    forallProp (e : Expr)
  | /-- Exists-propagator. -/
    existsProp (e : Expr)
  | /-- Input goal -/
    input
  | /-- Injectivity theorem. -/
    inj (origin : Origin)
  | /-- `grind_pattern` guard -/
    guard (origin : Origin)
  deriving Inhabited

def SplitSource.toMessageData : SplitSource → MessageData
  | .ematch origin => m!"E-matching `{origin.pp}`"
  | .guard origin => m!"Theorem instantiation guard for `{origin.pp}`"
  | .ext declName => m!"Extensionality `{declName}`"
  | .mbtc a b i => m!"Model-based theory combination at argument #{i} of{indentExpr a}\nand{indentExpr b}"
  | .beta e => m!"Beta-reduction of{indentExpr e}"
  | .forallProp e => m!"Forall propagation at{indentExpr e}"
  | .existsProp e => m!"Exists propagation at{indentExpr e}"
  | .input => "Initial goal"
  | .inj origin => m!"Injectivity `{origin.pp}`"

/-- Context for `GrindM` monad. -/
structure Context where
  simp         : Simp.Context
  simpMethods  : Simp.Methods
  config       : Grind.Config
  /--
  If `anchorRefs? := some anchorRefs`, then only local instances and case-splits in `anchorRefs`
  are considered.
  -/
  anchorRefs?  : Option (Array AnchorRef)
  /--
  If `cheapCases` is `true`, `grind` only applies `cases` to types that contain
  at most one minor premise.
  Recall that `grind` applies `cases` when introducing types tagged with `[grind cases eager]`,
  and at `Split.lean`
  Remark: We add this option to implement the `lookahead` feature, we don't want to create several subgoals
  when performing lookahead.
  -/
  cheapCases : Bool := false
  /-
  If `reportMVarIssue` is `true`, `grind` reports an issue when internalizing metavariables.
  The default value is `true`. We set it to `false` when invoking `proveEq` from the `instantiateTheorem`
  at in the E-matching module. There, the terms may contain metavariables, and we don't want to bother
  user with "false-alarms". If the instantiation fails, we produce a more informative issue anyways.
  -/
  reportMVarIssue : Bool := true
  /-- Current source of case-splits. -/
  splitSource  : SplitSource := .input
  /-- Symbol priorities for inferring E-matching patterns -/
  symPrios     : SymbolPriorities
  extensions   : ExtensionStateArray := #[]
  trueExpr     : Expr
  falseExpr    : Expr
  natZExpr     : Expr
  btrueExpr    : Expr
  bfalseExpr   : Expr
  ordEqExpr    : Expr -- `Ordering.eq`
  intExpr      : Expr -- `Int`
  debug        : Bool -- Cached `grind.debug (← getOptions)`

/-- Key for the congruence theorem cache. -/
structure CongrTheoremCacheKey where
  f       : Expr
  numArgs : Nat

-- We manually define `BEq` because we want to use pointer equality.
instance : BEq CongrTheoremCacheKey where
  beq a b := isSameExpr a.f b.f && a.numArgs == b.numArgs

-- We manually define `Hashable` because we want to use pointer equality.
instance : Hashable CongrTheoremCacheKey where
  hash a := mixHash (hashPtrExpr a.f) (hash a.numArgs)

structure Counters where
  /-- Number of times E-match theorem has been instantiated. -/
  thm  : PHashMap Origin Nat := {}
  /-- Number of times a `cases` has been performed on an inductive type/predicate -/
  case : PHashMap Name Nat := {}
  /-- Number of applications per function symbol. This information is only collected if `set_option diagnostics true` -/
  apps : PHashMap Name Nat := {}
  deriving Inhabited

private def emptySC : ShareCommon.State.{0} ShareCommon.objectFactory := ShareCommon.State.mk _

/-- Case-split diagnostic information -/
structure SplitDiagInfo where
  lctx        : LocalContext
  c           : Expr
  gen         : Nat
  numCases    : Nat
  splitSource : SplitSource

/-- State for the `GrindM` monad. -/
structure State where
  /--
  Congruence theorems generated so far. Recall that for constant symbols
  we rely on the reserved name feature (i.e., `mkHCongrWithArityForConst?`).
  Remark: we currently do not reuse congruence theorems
  -/
  congrThms  : PHashMap CongrTheoremCacheKey CongrTheorem := {}
  simp       : Simp.State := {}
  /--
  Used to generate trace messages of the for `[grind] working on <tag>`,
  and implement the macro `trace_goal`.
  -/
  lastTag    : Name := .anonymous
  /--
  Issues found during the proof search. These issues are reported to
  users when `grind` fails.
  -/
  issues     : List MessageData := []
  /-- Performance counters -/
  counters   : Counters := {}
  /-- Split diagnostic information. This information is only collected when `set_option diagnostics true` -/
  splitDiags : PArray SplitDiagInfo := {}
  /--
  Mapping from binary functions `f` to a theorem `thm : ∀ a b, f a b = .eq → a = b`
  if it implements the `LawfulEqCmp` type class.
  -/
  lawfulEqCmpMap : PHashMap ExprPtr (Option Expr) := {}
  /--
  Mapping from binary functions `f` to a theorem `thm : ∀ a, f a a = .eq`
  if it implements the `ReflCmp` type class.
  -/
  reflCmpMap : PHashMap ExprPtr (Option Expr) := {}
  /--
  Cached anchors (aka stable hash codes) for terms in the `grind` state.
  -/
  anchors : PHashMap ExprPtr UInt64 := {}

instance : Nonempty State :=
  .intro {}

private opaque MethodsRefPointed : NonemptyType.{0}
def MethodsRef : Type := MethodsRefPointed.type
instance : Nonempty MethodsRef := by exact MethodsRefPointed.property

abbrev GrindM := ReaderT MethodsRef $ ReaderT Context $ StateRefT State Sym.SymM

@[inline] def mapGrindM [MonadControlT GrindM m] [Monad m] (f : {α : Type} → GrindM α → GrindM α) {α} (x : m α) : m α :=
  controlAt GrindM fun runInBase => f <| runInBase x

/-- Returns `true` if `grind.debug` is set -/
@[inline] def isDebugEnabled : GrindM Bool :=
  return (← readThe Context).debug

/--
Backtrackable state for the `GrindM` monad.
-/
structure SavedState where
  «meta» : Meta.SavedState
  grind  : State
  deriving Nonempty

protected def saveState : GrindM SavedState :=
  return { «meta» := (← Meta.saveState), grind := (← get) }

/-- Restore backtrackable parts of the state. -/
def SavedState.restore (b : SavedState) : GrindM Unit := do
  b.meta.restore
  set b.grind

instance : MonadBacktrack SavedState GrindM where
  saveState      := Grind.saveState
  restoreState s := s.restore

/--
`withoutReportingMVarIssues x` executes `x` without reporting metavariables found during internalization.
See comment at `Grind.Context.reportMVarIssue` for additional details.
-/
def withoutReportingMVarIssues [MonadControlT GrindM m] [Monad m] : m α → m α :=
  mapGrindM <| withTheReader Grind.Context fun ctx => { ctx with reportMVarIssue := false }

/--
`withSplitSource s x` executes `x` and uses `s` as the split source for any case-split
registered.
-/
def withSplitSource [MonadControlT GrindM m] [Monad m] (splitSource : SplitSource) : m α → m α :=
  mapGrindM <| withTheReader Grind.Context fun ctx => { ctx with splitSource }

/-- Returns the user-defined configuration options -/
def getConfig : GrindM Grind.Config :=
  return (← readThe Context).config

/-- Returns extension states associate with `grind` attributes in use -/
def getExtensions : GrindM Grind.ExtensionStateArray :=
  return (← readThe Context).extensions

/--
Runs `k` with the transparency setting specified by `Config.reducible`.
Uses reducible transparency if `reducible` is `true`, otherwise default transparency.
-/
abbrev withGTransparency [MonadControlT MetaM n] [MonadLiftT GrindM n] [Monad n] (k : n α) : n α := do
  let m := if (← getConfig).reducible then .reducible else .default
  withTransparency m k

/-- Returns the internalized `True` constant.  -/
def getTrueExpr : GrindM Expr := do
  return (← readThe Context).trueExpr

/-- Returns the internalized `False` constant.  -/
def getFalseExpr : GrindM Expr := do
  return (← readThe Context).falseExpr

/-- Returns the internalized `Bool.true`.  -/
def getBoolTrueExpr : GrindM Expr := do
  return (← readThe Context).btrueExpr

/-- Returns the internalized `Bool.false`.  -/
def getBoolFalseExpr : GrindM Expr := do
  return (← readThe Context).bfalseExpr

/-- Returns the internalized `0 : Nat` numeral.  -/
def getNatZeroExpr : GrindM Expr := do
  return (← readThe Context).natZExpr

/-- Returns the internalized `Ordering.eq`.  -/
def getOrderingEqExpr : GrindM Expr := do
  return (← readThe Context).ordEqExpr

/-- Returns the internalized `Int`.  -/
def getIntExpr : GrindM Expr := do
  return (← readThe Context).intExpr

/-- Returns the anchor references (if any) being used to restrict the search. -/
def getAnchorRefs : GrindM (Option (Array AnchorRef)) := do
  return (← readThe Context).anchorRefs?

def resetAnchors : GrindM Unit := do
  modify fun s => { s with anchors := {} }

def cheapCasesOnly : GrindM Bool :=
  return (← readThe Context).cheapCases

def withCheapCasesOnly (k : GrindM α) : GrindM α :=
  withTheReader Grind.Context (fun ctx => { ctx with cheapCases := true }) k

def reportMVarInternalization : GrindM Bool :=
  return (← readThe Context).reportMVarIssue

/-- Returns symbol priorities for inferring E-matching patterns. -/
def getSymbolPriorities : GrindM SymbolPriorities := do
  return (← readThe Context).symPrios

/--
Returns `true` if we `declName` is tagged with `funCC` modifier.
-/
def hasFunCCModifier (declName : Name) : GrindM Bool :=
  return (← readThe Context).extensions.any fun ext => ext.funCC.contains declName

def isSplit (declName : Name) : GrindM Bool :=
  return (← readThe Context).extensions.any fun ext => ext.casesTypes.isSplit declName

def isEagerSplit (declName : Name) : GrindM Bool :=
  return (← readThe Context).extensions.any fun ext => ext.casesTypes.isEagerSplit declName

def isExtTheorem (declName : Name) : GrindM Bool :=
  return (← readThe Context).extensions.any fun ext => ext.extThms.contains declName

/--
Returns `true` if `declName` is the name of a `match` equation or a `match` congruence equation.
-/
def isMatchEqLikeDeclName (declName : Name) : CoreM Bool := do
  return (← isMatchCongrEqDeclName declName) || Match.isMatchEqnTheorem (← getEnv) declName

private def incCounter [Hashable α] [BEq α] (s : PHashMap α Nat) (k : α) : PHashMap α Nat :=
  if let some n := s.find? k then
      s.insert k (n+1)
    else
      s.insert k 1

private def saveEMatchTheorem (thm : EMatchTheorem) : GrindM Unit := do
  modify fun s => { s with counters.thm := incCounter s.counters.thm thm.origin }

def getEMatchTheoremNumInstances (thm : EMatchTheorem) : GrindM Nat := do
  return (← get).counters.thm.find? thm.origin |>.getD 0

def saveCases (declName : Name) : GrindM Unit := do
  modify fun s => { s with counters.case := incCounter s.counters.case declName }

def saveAppOf (h : HeadIndex) : GrindM Unit := do
  if (← isDiagnosticsEnabled) then
    let .const declName := h | return ()
    modify fun s => { s with counters.apps := incCounter s.counters.apps declName }

def saveSplitDiagInfo (c : Expr) (gen : Nat) (numCases : Nat) (splitSource : SplitSource) : GrindM Unit := do
  if (← isDiagnosticsEnabled) then
    let lctx ← getLCtx
    modify fun s => { s with splitDiags := s.splitDiags.push { c, gen, lctx, numCases, splitSource } }

@[inline] def getMethodsRef : GrindM MethodsRef :=
  read

/-- Returns maximum term generation that is considered during ematching. -/
def getMaxGeneration : GrindM Nat := do
  return (← getConfig).gen

/--
Abstracts nested proofs in `e`. This is a preprocessing step performed before internalization.
-/
def abstractNestedProofs (e : Expr) : GrindM Expr :=
  Meta.abstractNestedProofs e

/-- Returns `true` if `e` is the internalized `True` expression.  -/
def isTrueExpr (e : Expr) : GrindM Bool :=
  return isSameExpr e (← getTrueExpr)

/-- Returns `true` if `e` is the internalized `False` expression.  -/
def isFalseExpr (e : Expr) : GrindM Bool :=
  return isSameExpr e (← getFalseExpr)

/--
Creates a congruence theorem for a `f`-applications with `numArgs` arguments.
-/
def mkHCongrWithArity (f : Expr) (numArgs : Nat) : GrindM CongrTheorem := do
  let key := { f, numArgs }
  if let some result := (← get).congrThms.find? key then
    return result
  if let .const declName us := f then
    if let some result ← withDefault <| Meta.mkHCongrWithArityForConst? declName us numArgs then
      modify fun s => { s with congrThms := s.congrThms.insert key result }
      return result
  let result ← withDefault <| Meta.mkHCongrWithArity f numArgs
  modify fun s => { s with congrThms := s.congrThms.insert key result }
  return result

def reportIssue (msg : MessageData) : GrindM Unit := do
  let msg ← addMessageContext msg
  modify fun s => { s with issues := .trace { cls := `issue } msg #[] :: s.issues }
  /-
  We also add a trace message because we may want to know when
  an issue happened relative to other trace messages.
  -/
  trace[grind.issues] msg

private meta def expandReportIssueMacro (s : Syntax) : MacroM (TSyntax `doElem) := do
  let msg ← if s.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| do
    if (← getConfig).verbose then
      reportIssue $msg)

macro "reportIssue!" s:(interpolatedStr(term) <|> term) : doElem => do
  expandReportIssueMacro s.raw

/-- Similar to `expandReportIssueMacro`, but only reports issue if `grind.debug` is set to `true` -/
meta def expandReportDbgIssueMacro (s : Syntax) : MacroM (TSyntax `doElem) := do
  let msg ← if s.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| do
    if (← getConfig).verbose then
      if grind.debug.get (← getOptions) then
        reportIssue $msg)

/-- Similar to `reportIssue!`, but only reports issue if `grind.debug` is set to `true` -/
macro "reportDbgIssue!" s:(interpolatedStr(term) <|> term) : doElem => do
  expandReportDbgIssueMacro s.raw

/--
Each E-node may have "solver terms" attached to them.
Each term is an element of the equivalence class that the
solver cares about. Each solver is responsible for marking the terms they care about.
The `grind` core propagates equalities and disequalities to the theory solvers
using these "marked" terms. The root of the equivalence class
contains a list of representatives sorted by solver id. Note that many E-nodes
do not have any solver terms attached to them.

"Solver terms" are referenced as "theory variables" in the SMT literature.
The SMT solver Z3 uses a similar representation.
-/
inductive SolverTerms where
  | nil
  | next (solverId : Nat) (e : Expr) (rest : SolverTerms)
  deriving Inhabited, Repr

/--
Stores information for a node in the E-graph.
Each internalized expression `e` has an `ENode` associated with it.
-/
structure ENode where
  /-- Node represented by this ENode. -/
  self : Expr
  /-- Next element in the equivalence class. -/
  next : Expr
  /-- Root (aka canonical representative) of the equivalence class -/
  root : Expr
  /--
  `congr` is the term `self` is congruent to.
  We say `self` is the congruence class root if `isSameExpr congr self`.
  This field is initialized to `self` even if `e` is not an application.
  -/
  congr : Expr
  /--
  When `e` was added to this equivalence class because of an equality `h : e = target`,
  then we store `target` here, and `h` at `proof?`.
  -/
  target? : Option Expr := none
  proof? : Option Expr := none
  /-- Proof has been flipped. -/
  flipped : Bool := false
  /-- Number of elements in the equivalence class, this field is meaningless if node is not the root. -/
  size : Nat := 1
  /-- `interpreted := true` if node should be viewed as an abstract value. -/
  interpreted : Bool := false
  /-- `ctor := true` if the head symbol is a constructor application. -/
  ctor : Bool := false
  /-- `hasLambdas := true` if the equivalence class contains lambda expressions. -/
  hasLambdas : Bool := false
  /--
  If `heqProofs := true`, then some proofs in the equivalence class are based
  on heterogeneous equality.
  -/
  heqProofs : Bool := false
  /-- Unique index used for pretty printing and debugging purposes. -/
  idx : Nat := 0
  /-- The generation in which this enode was created. -/
  generation : Nat := 0
  /-- Modification time -/
  mt : Nat := 0
  /-- Solver terms attached to this E-node. -/
  sTerms : SolverTerms := .nil
  /--
  If `funCC := true`, then the expression associated with this entry is an application, and
  function congruence closure is enabled for it.
  See `Grind.Config.funCC` for additional details.
  -/
  funCC : Bool := true
  deriving Inhabited, Repr

def ENode.isRoot (n : ENode) :=
  isSameExpr n.self n.root

def ENode.isCongrRoot (n : ENode) :=
  isSameExpr n.self n.congr

/-- New equalities and facts to be processed. -/
inductive NewFact where
  | eq (lhs rhs proof : Expr) (isHEq : Bool)
  | fact (prop proof : Expr) (generation : Nat)

def NewFact.toExpr : NewFact → MetaM Expr
  | .eq lhs rhs _ _ => mkEq lhs rhs
  | .fact p _ _ => return p

-- This type should be considered opaque outside this module.
@[expose]  -- for codegen
def ENodeMap := PHashMap ExprPtr ENode
instance : Inhabited ENodeMap where
  default := private (id {})  -- TODO(sullrich): `id` works around `private` not respecting the expected type

/--
Key for the congruence table.
We need access to the `enodes` to be able to retrieve the equivalence class roots.
-/
structure CongrKey (enodes : ENodeMap) where
  e : Expr

private def hashRoot (enodes : ENodeMap) (e : Expr) : UInt64 :=
  if let some node := enodes.find? { expr := e } then
    hashPtrExpr node.root
  else
    hashPtrExpr e

private def hasSameRoot (enodes : ENodeMap) (a b : Expr) : Bool := Id.run do
  if isSameExpr a b then
    return true
  else
    let some n1 := enodes.find? { expr := a } | return false
    let some n2 := enodes.find? { expr := b } | return false
    isSameExpr n1.root n2.root

private def useFunCC' (enodes : ENodeMap) (e : Expr) : Bool :=
  if let some n := enodes.find? { expr := e } then
    n.funCC
  else
    false

private def congrHash (enodes : ENodeMap) (e : Expr) : UInt64 :=
  if let .forallE _ d b _ := e then
    mixHash (hashRoot enodes d) (hashRoot enodes b)
  else match_expr e with
  | Grind.nestedProof p _ => hashRoot enodes p
  | Grind.nestedDecidable p _ => mixHash 13 (hashRoot enodes p)
  | Eq _ lhs rhs => goEq lhs rhs
  | _ =>
    match e with
    | .app f a =>
      if useFunCC' enodes e then
        mixHash (hashRoot enodes f) (hashRoot enodes a)
      else
        go f (hashRoot enodes a)
    | _ => hashRoot enodes e
where
  goEq (lhs rhs : Expr) : UInt64 :=
    let h₁ := hashRoot enodes lhs
    let h₂ := hashRoot enodes rhs
    if h₁ > h₂ then mixHash h₂ h₁ else mixHash h₁ h₂
  go (e : Expr) (r : UInt64) : UInt64 :=
    match e with
    | .app f a => go f (mixHash r (hashRoot enodes a))
    | _ => mixHash r (hashRoot enodes e)

/-- Returns `true` if `e₁` and `e₂` are congruent modulo the equivalence classes in `enodes`. -/
private partial def isCongruent (enodes : ENodeMap) (e₁ e₂ : Expr) : Bool :=
  if let .forallE _ d₁ b₁ _ := e₁ then
    if let .forallE _ d₂ b₂ _ := e₂ then
      hasSameRoot enodes d₁ d₂ && hasSameRoot enodes b₁ b₂
    else
      false
  else match_expr e₁ with
  | Grind.nestedProof p₁ _ =>
    let_expr Grind.nestedProof p₂ _ := e₂ | false
    hasSameRoot enodes p₁ p₂
  | Grind.nestedDecidable p₁ _ =>
    let_expr Grind.nestedDecidable p₂ _ := e₂ | false
    hasSameRoot enodes p₁ p₂
  | Eq _ lhs₁ rhs₁ =>
    let_expr Eq _ lhs₂ rhs₂ := e₂ | false
    goEq lhs₁ rhs₁ lhs₂ rhs₂
  | _ => Id.run do
    let .app f a := e₁ | return false
    let .app g b := e₂ | return false
    if useFunCC' enodes e₁ then
      /-
      **Note**: We are not in `MetaM` here. Thus, we cannot check whether `f` and `g` have the same type.
      So, we approximate and try to handle this issue when generating the proof term.
      -/
      hasSameRoot enodes a b && hasSameRoot enodes f g
    else
      hasSameRoot enodes a b && go f g
where
  goEq (lhs₁ rhs₁ lhs₂ rhs₂ : Expr) : Bool :=
    (hasSameRoot enodes lhs₁ lhs₂ && hasSameRoot enodes rhs₁ rhs₂)
    ||
    (hasSameRoot enodes lhs₁ rhs₂ && hasSameRoot enodes rhs₁ lhs₂)
  go (a b : Expr) : Bool :=
    if a.isApp && b.isApp then
      hasSameRoot enodes a.appArg! b.appArg! && go a.appFn! b.appFn!
    else
      -- Remark: we do not check whether the types of the functions are equal here
      -- because we are not in the `MetaM` monad.
      hasSameRoot enodes a b

instance : Hashable (CongrKey enodeMap) where
  hash k := private congrHash enodeMap k.e

instance : BEq (CongrKey enodeMap) where
  beq k1 k2 := private isCongruent enodeMap k1.e k2.e

abbrev CongrTable (enodeMap : ENodeMap) := PHashSet (CongrKey enodeMap)

/-
**Note**: If inserting elements in a `ParentSet` becomes a performance bottleneck,
we can add an extra field `Std.HashSet ExprPtr` for detecting whether the `ParentSet` already
contains an element or not.

**Note**: We used to implement `ParentSet`s as
```abbrev ParentSet := Std.TreeSet Expr Expr.quickComp```
This representation created proof stability issues.
For example, we traverse this set to implement congruence closure.
There is no non-determinism here, but the traversal depends on the `Expr`
hash code, which is very sensitive to changes in a `.lean` file.
Thus, minor changes may affect the proof found by `grind`. We found examples
where proving the same goal multiple times in the same file produced different
proofs.
When we inspected the hash codes, they were completely different.
Using `Expr.comp` does not help because it still relies on internal free variable IDs.
One might think we can just reset them at the beginning of the `grind` search, but
this is not sufficient. When tactics such as `finish?` generate the final tactic
script, we remove unnecessary case splits. Removing case splits affects the generated
free variable IDs, which in turn affects the result of Expr.comp :(
-/
structure ParentSet where
  parents : List Expr := []
  deriving Inhabited

def ParentSet.insert (ps : ParentSet) (p : Expr) : ParentSet :=
  { ps with parents := ps.parents.insert p }

def ParentSet.isEmpty (ps : ParentSet) : Bool :=
  ps.parents.isEmpty

def ParentSet.elems (ps : ParentSet) : List Expr :=
  ps.parents

abbrev ParentMap := PHashMap ExprPtr ParentSet

/--
The E-matching module instantiates theorems using the `EMatchTheorem proof` and a (partial) assignment.
We want to avoid instantiating the same theorem with the same assignment more than once.
Therefore, we store the (pre-)instance information in set.
Recall that the proofs of activated theorems have been hash-consed.
The assignment contains internalized expressions, which have also been hash-consed.

**Note**: We used to use pointer equality to implement `PreInstanceSet`. However,
this low-level trick was incorrect in interactive mode because we add new
`EMatchTheorem` objects using `instantiate [...]`. For example, suppose we write
```
instantiate [thm_1]; instantiate [thm_1]
```
The `EMatchTheorem` object `thm_1` is created twice. Using pointer equality will
miss instances created using the two different objects. Recall we do not use
hash-consing on proof objects. If we hash-cons the proof objects, it would be ok
to use pointer equality.
-/
structure PreInstance where
  proof      : Expr
  assignment : Array Expr

instance : Hashable PreInstance where
  hash i := Id.run do
    let mut r := hash i.proof -- **Note**: See note at `PreInstance`.
    for v in i.assignment do
      r := mixHash r (hashPtrExpr v)
    return r

instance : BEq PreInstance where
  beq i₁ i₂ := Id.run do
    unless i₁.proof == i₂.proof do return false -- **Note**: See note at `PreInstance`.
    unless i₁.assignment.size == i₂.assignment.size do return false
    for v₁ in i₁.assignment, v₂ in i₂.assignment do
      unless isSameExpr v₁ v₂ do return false
    return true

abbrev PreInstanceSet := PHashSet PreInstance

/-- New raw fact to be preprocessed, and then asserted. -/
structure NewRawFact where
  proof        : Expr
  prop         : Expr
  generation   : Nat
  /-- `splitSource` to use when internalizing this fact. -/
  splitSource  : SplitSource
  deriving Inhabited

structure CanonArgKey where
  f   : Expr
  i   : Nat
  arg : Expr
  deriving BEq, Hashable

/-- Canonicalizer state. See `Canon.lean` for additional details. -/
structure Canon.State where
  argMap     : PHashMap (Expr × Nat) (List (Expr × Expr)) := {}
  canon      : PHashMap Expr Expr := {}
  proofCanon : PHashMap Expr Expr := {}
  canonArg   : PHashMap CanonArgKey Expr := {}
  deriving Inhabited

/-- Trace information for a case split. -/
structure CaseTrace where
  expr   : Expr
  i      : Nat
  num    : Nat
  source : SplitSource
  deriving Inhabited

/--
Users can attach guards to `grind_pattern`s. A guard ensures that a theorem is instantiated
 only when the guard expression becomes provably true.

If `check` is `true`, then `grind` attempts to prove `e` by asserting its negation and
checking whether this leads to a contradiction.
-/
structure TheoremGuard where
  e     : Expr
  check : Bool
  deriving Inhabited

/--
A delayed theorem instantiation is an instantiation that includes one or more guards.
See `TheoremGuard`.
-/
structure DelayedTheoremInstance where
  thm        : EMatchTheorem
  proof      : Expr
  prop       : Expr
  generation : Nat
  guards     : List TheoremGuard
  deriving Inhabited

/-- E-matching related fields for the `grind` goal. -/
structure EMatch.State where
  /--
  Inactive global theorems. As we internalize terms, we activate theorems as we find their symbols.
  Local theorem provided by users are added directly into `newThms`.
  -/
  thmMap       : EMatchTheoremsArray
  /-- Goal modification time. -/
  gmt          : Nat := 0
  /-- Active theorems that we have performed ematching at least once. -/
  thms         : PArray EMatchTheorem := {}
  /-- Active theorems that we have not performed any round of ematching yet. -/
  newThms      : PArray EMatchTheorem := {}
  /-- Number of theorem instances generated so far. -/
  numInstances : Nat := 0
  /-- Number of delayed theorem instances generated so far. We track them to decide whether E-match made progress or not. -/
  numDelayedInstances : Nat := 0
  /-- Number of E-matching rounds performed in this goal since the last case-split. -/
  num          : Nat := 0
  /-- (pre-)instances found so far. It includes instances that failed to be instantiated. -/
  preInstances : PreInstanceSet := {}
  /-- Next local E-match theorem idx. -/
  nextThmIdx   : Nat := 0
  /-- `match` auxiliary functions whose equations have already been created and activated. -/
  matchEqNames : PHashSet Name := {}
  /--
  Delayed instantiations is a mapping from guards to theorems that are waiting them
  to become `True`.
  -/
  delayedThmInsts : PHashMap ExprPtr (List DelayedTheoremInstance) := {}
  deriving Inhabited

/-- Case-split information. -/
inductive SplitInfo where
  | /--
    Term `e` may be an inductive predicate, `match`-expression, `if`-expression, implication, etc.
    -/
    default (e : Expr) (source : SplitSource)
  /-- `e` is an implication and we want to split on its antecedent. -/
  | imp (e : Expr) (h : e.isForall) (source : SplitSource)
  | /--
    Given applications `a` and `b`, case-split on whether the corresponding
    `i`-th arguments are equal or not. The split is only performed if all other
    arguments are already known to be equal or are also tagged as split candidates.
    -/
    arg (a b : Expr) (i : Nat) (eq : Expr) (source :SplitSource)
  deriving Inhabited

protected def SplitInfo.hash : SplitInfo → UInt64
 | .default e _ => hash e
 | .imp e _ _   => hash e
 | .arg _ _ _ e _ => hash e

instance : Hashable SplitInfo where
  hash := SplitInfo.hash

def SplitInfo.beq : SplitInfo → SplitInfo → Bool
 | .default e₁ _, .default e₂ _ => e₁ == e₂
 | .imp e₁ _ _, .imp e₂ _ _=> e₁ == e₂
 | .arg a₁ b₁ i₁ eq₁ _, arg a₂ b₂ i₂ eq₂ _ => a₁ == a₂ && b₁ == b₂ && i₁ == i₂ && eq₁ == eq₂
 | _, _ => false

instance : BEq SplitInfo where
  beq := SplitInfo.beq

def SplitInfo.getExpr : SplitInfo → Expr
  | .default e _ => e
  | .imp e h _ => e.forallDomain h
  | .arg _ _ _ eq _ => eq

def SplitInfo.source : SplitInfo → SplitSource
  | .default _ s   => s
  | .imp _ _ s     => s
  | .arg _ _ _ _ s => s

def SplitInfo.lt : SplitInfo → SplitInfo → Bool
  | .default e₁ _, .default e₂ _     => e₁.lt e₂
  | .imp e₁ _ _, .imp e₂ _ _         => e₁.lt e₂
  | .arg _ _ _ e₁ _, .arg _ _ _ e₂ _ => e₁.lt e₂
  | .default .., _                   => true
  | .imp .., _                       => true
  | _, _                             => false

/-- Argument `arg : type` of an application `app` in `SplitInfo`. -/
structure SplitArg where
  arg  : Expr
  type : Expr
  app  : Expr

/-- Case splitting related fields for the `grind` goal. -/
structure Split.State where
  /-- Number of splits performed to get to this goal. -/
  num          : Nat := 0
  /-- Case-split candidates. -/
  candidates   : List SplitInfo := []
  /-- Case-splits that have been inserted at `candidates` at some point. -/
  added        : Std.HashSet SplitInfo := {}
  /-- Case-splits that have already been performed, or that do not have to be performed anymore. -/
  resolved     : PHashSet ExprPtr := {}
  /--
  Sequence of cases steps that generated this goal. We only use this information for diagnostics.
  Remark: `casesTrace.length ≥ numSplits` because we don't increase the counter for `cases`
  applications that generated only 1 subgoal.
  -/
  trace        : List CaseTrace := []
  /-- Lookahead "case-splits". -/
  lookaheads   : List SplitInfo := []
  /--
  A mapping `(a, b) ↦ is` s.t. for each `SplitInfo.arg a b i eq`
  in `candidates` or `lookaheads` we have `i ∈ is`.
  We use this information to decide whether the split/lookahead is "ready"
  to be tried or not.
  -/
  argPosMap    : Std.HashMap (Expr × Expr) (List Nat) := {}
  /--
  Mapping from pairs `(f, i)` to a list of arguments.
  Each argument occurs as the `i`-th of an `f`-application.
  We use this information to add splits/lookaheads for
  triggering extensionality theorems and model-based theory combination.
  See `addSplitCandidatesForExt`.
  -/
  argsAt       : PHashMap (Expr × Nat) (List SplitArg) := {}
  deriving Inhabited

/-- Clean name generator. -/
structure Clean.State where
  used : PHashSet Name := {}
  next : PHashMap Name Nat := {}
  deriving Inhabited

/--
Cache for `Unit`-like types. It maps the type to its element.
We say a type is `Unit`-like if it is a subsingleton and is inhabited.
-/
structure UnitLike.State where
  map : PHashMap ExprPtr (Option Expr) := {}
  deriving Inhabited

structure InjectiveInfo where
  us   : List Level
  α    : Expr
  β    : Expr
  h    : Expr
  /--
  Inverse function and a proof that `∀ a, inv (f a) = a`
  **Note**: The following two fields are `none` if no `f`-application has been found yet.
  -/
  inv?  : Option (Expr × Expr) := none
  deriving Inhabited

/-- State for injective theorem support. -/
structure Injective.State where
  thms : InjectiveTheoremsArray
  fns  : PHashMap ExprPtr InjectiveInfo := {}
  deriving Inhabited

/--
The `grind` state for a goal, excluding the metavariable.

This separation from `Goal` allows multiple goals with different metavariables to share
the same `GoalState`. This is useful for automation such as symbolic simulation, where applying
theorems create multiple goals that inherit the same E-graph, congruence closure state, and other
accumulated facts.
-/
structure GoalState where
  /-- Next local declaration index to process. -/
  nextDeclIdx  : Nat := 0
  canon        : Canon.State := {}
  enodeMap     : ENodeMap := default
  exprs        : PArray Expr := {}
  parents      : ParentMap := {}
  congrTable   : CongrTable enodeMap := {}
  /--
  A mapping from each function application index (`HeadIndex`) to a list of applications with that index.
  Recall that the `HeadIndex` for a constant is its constant name, and for a free variable,
  it is its unique id.
  -/
  appMap       : PHashMap HeadIndex (List Expr) := {}
  /--
  All constants (*not* in `appMap`) that have been internalized, *and*
  `appMap`'s domain. We use this collection during theorem activation.
  -/
  indicesFound : PHashSet HeadIndex := {}
  /-- Equations and propositions to be processed. -/
  newFacts     : Array NewFact := #[]
  /-- `inconsistent := true` if `ENode`s for `True` and `False` are in the same equivalence class. -/
  inconsistent : Bool := false
  /-- Next unique index for creating ENodes -/
  nextIdx      : Nat := 0
  /-- new facts to be preprocessed and then asserted. -/
  newRawFacts  : Std.Queue NewRawFact := ∅
  /-- Asserted facts -/
  facts        : PArray Expr := {}
  /-- Cached extensionality theorems for types. -/
  extThms      : PHashMap ExprPtr (Array Ext.ExtTheorem) := {}
  /-- State of the E-matching module. -/
  ematch       : EMatch.State
  /-- State of the injective function procedure. -/
  inj          : Injective.State
  /-- State of the case-splitting module. -/
  split        : Split.State := {}
  /-- State of the clean name generator. -/
  clean        : Clean.State := {}
  /-- Solver states. -/
  sstates      : Array SolverExtensionState := #[]
  deriving Inhabited

/--
A `grind` goal, combining shared state with a specific metavariable.

See `GoalState` for details on why the state is factored out.
**Note**: The `Goal` internal representation is just a pair `GoalState` and `MVarId`.
-/
structure Goal extends GoalState where
  mvarId : MVarId
  deriving Inhabited

def Goal.hasSameRoot (g : Goal) (a b : Expr) : Bool :=
  Grind.hasSameRoot g.enodeMap a b

def Goal.isCongruent (g : Goal) (a b : Expr) : Bool :=
  Grind.isCongruent g.enodeMap a b

def Goal.admit (goal : Goal) : MetaM Unit :=
  goal.mvarId.admit

abbrev GoalM := StateRefT Goal GrindM

@[inline] def GoalM.runCore (goal : Goal) (x : GoalM α) : GrindM (α × Goal) :=
  StateRefT'.run x goal

@[inline] def GoalM.run (goal : Goal) (x : GoalM α) : GrindM (α × Goal) :=
  goal.mvarId.withContext do x.runCore goal

@[inline] def GoalM.run' (goal : Goal) (x : GoalM Unit) : GrindM Goal :=
  goal.mvarId.withContext do StateRefT'.run' (x *> get) goal

/--
Sets `nextDeclIdx` to point past the last local declaration in the local context.

This marks all existing local declarations as already processed by `grind`. Use this when
initializing a goal whose hypotheses should not be processed or after internalizing all of them.
-/
def Goal.setNextDeclToEnd (g : Goal) : MetaM Goal := do
  let mvarDecl ← g.mvarId.getDecl
  return { g with nextDeclIdx := mvarDecl.lctx.decls.size }

def setNextDeclToEnd : GoalM Unit := do
  let mvarDecl ← (← get).mvarId.getDecl
  modify fun g => { g with nextDeclIdx := mvarDecl.lctx.decls.size }

/--
Returns `true` if the goal has local declarations that have not yet been processed by `grind`.

A local declaration is "pending" if its index is greater than or equal to `nextDeclIdx`.
This is used to determine whether `grind` needs to internalize new hypotheses.
-/
def Goal.hasPendingLocalDecls (g : Goal) : MetaM Bool := do
  let mvarDecl ← g.mvarId.getDecl
  return g.nextDeclIdx < mvarDecl.lctx.decls.size

def updateLastTag : GoalM Unit := do
  if (← isTracingEnabledFor `grind) then
    let currTag ← (← get).mvarId.getTag
    if currTag != (← getThe Grind.State).lastTag then
      trace[grind] "working on goal `{currTag}`"
      modifyThe Grind.State fun s => { s with lastTag := currTag }

/--
Macro similar to `trace[...]`, but it includes the trace message `trace[grind] "working on <current goal>"`
if the tag has changed since the last trace message.
-/
macro "trace_goal[" id:ident "]" s:(interpolatedStr(term) <|> term) : doElem => do
  let msg ← if s.raw.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| do
    let cls := $(quote id.getId.eraseMacroScopes)
    if (← Lean.isTracingEnabledFor cls) then
      updateLastTag
      Lean.addTrace cls $msg)

/--
A helper function used to mark a theorem instance found by the E-matching module.
It returns `true` if it is a new instance and `false` otherwise.
-/
def markTheoremInstance (proof : Expr) (assignment : Array Expr) : GoalM Bool := do
  let k := { proof, assignment }
  if (← get).ematch.preInstances.contains k then
    return false
  modify fun s => { s with ematch.preInstances := s.ematch.preInstances.insert k }
  return true

/-- Adds a new fact `prop` with proof `proof` to the queue for preprocessing and the assertion. -/
def addNewRawFact (proof : Expr) (prop : Expr) (generation : Nat) (splitSource : SplitSource) : GoalM Unit := do
  if (← isDebugEnabled) then
    unless (← withGTransparency <| isDefEq (← inferType proof) prop) do
      throwError "`grind` internal error, trying to assert{indentExpr prop}\n\
        with proof{indentExpr proof}\nwhich has type{indentExpr (← inferType proof)}\n\
        which is not definitionally equal with `reducible` transparency setting"
  modify fun s => { s with newRawFacts := s.newRawFacts.enqueue { proof, prop, generation, splitSource } }

/-- Returns the number of theorem instances generated so far. -/
def getNumTheoremInstances : GoalM Nat := do
  return (← get).ematch.numInstances

/-- Returns `true` if the maximum number of instances has been reached. -/
def checkMaxInstancesExceeded : GoalM Bool := do
  return (← get).ematch.numInstances >= (← getConfig).instances

/-- Returns `true` if the maximum number of case-splits has been reached. -/
def checkMaxCaseSplit : GoalM Bool := do
  return (← get).split.num >= (← getConfig).splits

/-- Returns `true` if the maximum number of E-matching rounds has been reached. -/
def checkMaxEmatchExceeded : GoalM Bool := do
  return (← get).ematch.num >= (← getConfig).ematch

/--
Returns `some n` if `e` has already been "internalized" into the
Otherwise, returns `none`s.
-/
def Goal.getENode? (goal : Goal) (e : Expr) : Option ENode :=
  goal.enodeMap.find? { expr := e }

@[inline, inherit_doc Goal.getENode?]
def getENode? (e : Expr) : GoalM (Option ENode) :=
  return (← get).getENode? e

def throwNonInternalizedExpr (e : Expr) : MetaM α :=
  throwError "internal `grind` error, term has not been internalized{indentExpr e}"

/-- Returns node associated with `e`. It assumes `e` has already been internalized. -/
def Goal.getENode (goal : Goal) (e : Expr) : MetaM ENode := do
  let some n := goal.enodeMap.find? { expr := e }
    | throwNonInternalizedExpr e
  return n

@[inline, inherit_doc Goal.getENode]
def getENode (e : Expr) : GoalM ENode := do
  (← get).getENode e

def Goal.getGeneration (goal : Goal) (e : Expr) : Nat :=
  if let some n := goal.getENode? e then
    n.generation
  else
    0

def SplitInfo.getGenerationCore (goal : Goal) : SplitInfo → Nat
  | .default e _ => goal.getGeneration e
  | .imp e h _ => goal.getGeneration (e.forallDomain h)
  | .arg a b _ _ _ => max (goal.getGeneration a) (goal.getGeneration b)

def SplitInfo.getGeneration (s : SplitInfo) : GoalM Nat :=
  return s.getGenerationCore (← get)

/-- Returns the generation of the given term. Is assumes it has been internalized -/
def getGeneration (e : Expr) : GoalM Nat :=
  return (← get).getGeneration e

/-- Returns `true` if `e` is in the equivalence class of `True`. -/
def isEqTrue (e : Expr) : GoalM Bool := do
  return isSameExpr (← getENode e).root (← getTrueExpr)

/-- Returns `true` if `e` is in the equivalence class of `False`. -/
def isEqFalse (e : Expr) : GoalM Bool := do
  return isSameExpr (← getENode e).root (← getFalseExpr)

/-- Returns `true` if `e` is in the equivalence class of `Bool.true`. -/
def isEqBoolTrue (e : Expr) : GoalM Bool := do
  return isSameExpr (← getENode e).root (← getBoolTrueExpr)

/-- Returns `true` if `e` is in the equivalence class of `Bool.false`. -/
def isEqBoolFalse (e : Expr) : GoalM Bool := do
  return isSameExpr (← getENode e).root (← getBoolFalseExpr)

/-- Returns `true` if `a` and `b` are in the same equivalence class. -/
def isEqv (a b : Expr) : GoalM Bool := do
  if isSameExpr a b then
    return true
  else
    let some na ← getENode? a | return false
    let some nb ← getENode? b | return false
    return isSameExpr na.root nb.root

/-- Returns `true` if the root of its equivalence class. -/
def isRoot (e : Expr) : GoalM Bool := do
  let some n ← getENode? e | return false -- `e` has not been internalized. Panic instead?
  return isSameExpr n.root e

/-- Returns the root element in the equivalence class of `e` IF `e` has been internalized. -/
def Goal.getRoot? (goal : Goal) (e : Expr) : Option Expr := Id.run do
  let some n ← goal.getENode? e | return none
  return some n.root

@[inline, inherit_doc Goal.getRoot?]
def getRoot? (e : Expr) : GoalM (Option Expr) := do
  return (← get).getRoot? e

/-- Returns the root element in the equivalence class of `e`. -/
def Goal.getRoot (goal : Goal) (e : Expr) : MetaM Expr :=
  return (← goal.getENode e).root

@[inline, inherit_doc Goal.getRoot]
def getRoot (e : Expr) : GoalM Expr := do
  (← get).getRoot e

/-- Returns the root enode in the equivalence class of `e`. -/
def getRootENode (e : Expr) : GoalM ENode := do
  getENode (← getRoot e)

/-- Returns the root enode in the equivalence class of `e` if it is in an equivalence class. -/
def getRootENode? (e : Expr) : GoalM (Option ENode) := do
  let some n ← getENode? e | return none
  getENode? n.root
/--
Returns `true` if the ENode associate with `e` has support for function equality
congruence closure. See `Grind.Config.funCC` for additional details.
-/
def useFunCC (e : Expr) : GoalM Bool :=
  return (← getENode e).funCC

/--
Returns the next element in the equivalence class of `e`
if `e` has been internalized in the given goal.
-/
def Goal.getNext? (goal : Goal) (e : Expr) : Option Expr := Id.run do
  let some n ← goal.getENode? e | return none
  return some n.next

/-- Returns the next element in the equivalence class of `e`. -/
def Goal.getNext (goal : Goal) (e : Expr) : MetaM Expr :=
  return (← goal.getENode e).next

@[inline, inherit_doc Goal.getRoot]
def getNext (e : Expr) : GoalM Expr := do
  (← get).getNext e

/-- Returns `true` if `e` has already been internalized. -/
def alreadyInternalized (e : Expr) : GoalM Bool :=
  return (← get).enodeMap.contains { expr := e }

def Goal.getTarget? (goal : Goal) (e : Expr) : Option Expr := Id.run do
  let some n ← goal.getENode? e | return none
  return n.target?

@[inline] def getTarget? (e : Expr) : GoalM (Option Expr) := do
  return (← get).getTarget? e

/--
If `isHEq` is `false`, it pushes `lhs = rhs` with `proof` to `newEqs`.
Otherwise, it pushes `lhs ≍ rhs`.
-/
def pushEqCore (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  if (← isDebugEnabled) then
    unless (← alreadyInternalized lhs) do
      throwError "`grind` internal error, lhs of new equality has not been internalized{indentExpr lhs}"
    unless (← alreadyInternalized rhs) do
      throwError "`grind` internal error, rhs of new equality has not been internalized{indentExpr rhs}"
    if proof != congrPlaceholderProof && proof != eqCongrSymmPlaceholderProof then
      let expectedType ← if isHEq then mkHEq lhs rhs else mkEq lhs rhs
      unless (← withGTransparency <| isDefEq (← inferType proof) expectedType) do
        throwError "`grind` internal error, trying to assert equality{indentExpr expectedType}\n\
            with proof{indentExpr proof}\nwhich has type{indentExpr (← inferType proof)}\n\
            which is not definitionally equal with `reducible` transparency setting"
      trace[grind.debug] "pushEqCore: {expectedType}"
  modify fun s => { s with newFacts := s.newFacts.push <| .eq lhs rhs proof isHEq }

/-- Return `true` if `a` and `b` have the same type. -/
def hasSameType (a b : Expr) : MetaM Bool := do
  isDefEqD (← inferType a) (← inferType b)

@[inline] def pushEqHEq (lhs rhs proof : Expr) : GoalM Unit := do
  if (← hasSameType lhs rhs) then
    pushEqCore lhs rhs proof (isHEq := false)
  else
    pushEqCore lhs rhs proof (isHEq := true)

/-- Pushes `lhs = rhs` with `proof` to `newEqs`. -/
@[inline] def pushEq (lhs rhs proof : Expr) : GoalM Unit :=
  pushEqCore lhs rhs proof (isHEq := false)

/-- Pushes `lhs ≍ rhs` with `proof` to `newEqs`. -/
@[inline] def pushHEq (lhs rhs proof : Expr) : GoalM Unit :=
  pushEqCore lhs rhs proof (isHEq := true)

/-- Pushes `a = True` with `proof` to `newEqs`. -/
def pushEqTrue (a proof : Expr) : GoalM Unit := do
  pushEq a (← getTrueExpr) proof

/-- Pushes `a = False` with `proof` to `newEqs`. -/
def pushEqFalse (a proof : Expr) : GoalM Unit := do
  pushEq a (← getFalseExpr) proof

/-- Pushes `a = Bool.true` with `proof` to `newEqs`. -/
def pushEqBoolTrue (a proof : Expr) : GoalM Unit := do
  pushEq a (← getBoolTrueExpr) proof

/-- Pushes `a = Bool.false` with `proof` to `newEqs`. -/
def pushEqBoolFalse (a proof : Expr) : GoalM Unit := do
  pushEq a (← getBoolFalseExpr) proof

/--
Records that `parent` is a parent of `child`. This function actually stores the
information in the root (aka canonical representative) of `child`.
-/
def registerParent (parent : Expr) (child : Expr) : GoalM Unit := do
  let childRoot := (← getRoot? child).getD child
  let parents := if let some parents := (← get).parents.find? { expr := childRoot } then parents else {}
  modify fun s => { s with parents := s.parents.insert { expr := childRoot } (parents.insert parent) }

/--
Returns the set of expressions `e` is a child of, or an expression in
`e`s equivalence class is a child of.
The information is only up to date if `e` is the root (aka canonical representative) of the equivalence class.
-/
def getParents (e : Expr) : GoalM ParentSet := do
  let some parents := (← get).parents.find? { expr := e } | return {}
  return parents

/--
Removes the entry `e ↦ parents` from the parent map.
-/
def resetParentsOf (e : Expr) : GoalM Unit := do
  modify fun s => { s with parents := s.parents.erase { expr := e } }

/--
Copy `parents` to the parents of `root`.
`root` must be the root of its equivalence class.
-/
def copyParentsTo (parents : ParentSet) (root : Expr) : GoalM Unit := do
  let mut curr := if let some parents := (← get).parents.find? { expr := root } then parents else {}
  for parent in parents.elems do
    curr := curr.insert parent
  modify fun s => { s with parents := s.parents.insert { expr := root } curr }

def mkENodeCore (e : Expr) (interpreted ctor : Bool) (generation : Nat) (funCC : Bool) : GoalM Unit := do
  let n := {
    self := e, next := e, root := e, congr := e, size := 1
    flipped := false
    heqProofs := false
    hasLambdas := e.isLambda
    mt := (← get).ematch.gmt
    idx := (← get).nextIdx
    interpreted, ctor, generation, funCC
  }
  modify fun s => { s with
    enodeMap := s.enodeMap.insert { expr := e } n
    exprs := s.exprs.push e
    congrTable := unsafe unsafeCast s.congrTable
    nextIdx := s.nextIdx + 1
  }

/--
Creates an `ENode` for `e` if one does not already exist.
This method assumes `e` has been hash-consed.
-/
def mkENode (e : Expr) (generation : Nat) (funCC : Bool := false) : GoalM Unit := do
  if (← alreadyInternalized e) then return ()
  let ctor := (← isConstructorAppCore? e).isSome
  let interpreted ← isInterpreted e
  mkENodeCore e interpreted ctor generation funCC

def setENode (e : Expr) (n : ENode) : GoalM Unit :=
  modify fun s => { s with
    enodeMap := s.enodeMap.insert { expr := e } n
    congrTable := unsafe unsafeCast s.congrTable
  }

/--
Returns `true` if type of `t` is definitionally equal to `α`
-/
def hasType (t α : Expr) : MetaM Bool := do
  isDefEqD (← inferType t) α

/--
For each equality `b = c` in `parents`, executes `k b c` IF
- `b = c` is equal to `False`, and
-/
@[inline] def forEachDiseq (parents : ParentSet) (k : (lhs : Expr) → (rhs : Expr) → GoalM Unit) : GoalM Unit := do
  for parent in parents.elems do
    let_expr Eq _ b c := parent | continue
    if (← isEqFalse parent) then
      if (← isEqv b c) then
        /-
        Remark: if `b` and `c` are already in the same equivalence class,
        there is an inconsistency in the TODO queue already, and we can interrupt
        propagation
        -/
        return ()
      else
        k b c

/-- Returns `true` is `e` is the root of its congruence class. -/
def isCongrRoot (e : Expr) : GoalM Bool := do
  return (← getENode e).isCongrRoot

/-- Returns the root of the congruence class containing `e`. -/
partial def getCongrRoot (e : Expr) : GoalM Expr := do
  let n ← getENode e
  if isSameExpr n.congr e then return e
  getCongrRoot n.congr

/-- Return `true` if the goal is inconsistent. -/
def isInconsistent : GoalM Bool :=
  return (← get).inconsistent

/--
Returns a proof that `a = b`.
It assumes `a` and `b` are in the same equivalence class, and have the same type.
-/
-- Forward definition
@[extern "lean_grind_mk_eq_proof"]
opaque mkEqProof (a b : Expr) : GoalM Expr

/--
Returns a proof that `a ≍ b`.
It assumes `a` and `b` are in the same equivalence class.
-/
-- Forward definition
@[extern "lean_grind_mk_heq_proof"]
opaque mkHEqProof (a b : Expr) : GoalM Expr

-- Forward definition
@[extern "lean_grind_process_new_facts"]
opaque processNewFacts : GoalM Unit

-- Forward definition
@[extern "lean_grind_internalize"]
opaque internalize (e : Expr) (generation : Nat) (parent? : Option Expr := none) : GoalM Unit

-- Forward definition
@[extern "lean_grind_preprocess"]
opaque preprocess : Expr → GoalM Simp.Result

/--
Internalizes a local declaration which is not a proposition.
**Note**: We must internalize local variables because their types may be empty, and may not be
referenced anywhere else. Example:
```
example (a : { x : Int // x < 0 ∧ x > 0 }) : False := by grind
```
`etaStruct` may also be applicable.
-/
def internalizeLocalDecl (localDecl : LocalDecl) : GoalM Unit := do
  let e ← shareCommon localDecl.toExpr
  internalize e 0
  /-
  **Note**: `internalize` may add new facts (e.g., `etaStruct` equality)
  -/
  processNewFacts

/--
Returns a proof that `a = b` if they have the same type. Otherwise, returns a proof of `a ≍ b`.
It assumes `a` and `b` are in the same equivalence class.
-/
def mkEqHEqProof (a b : Expr) : GoalM Expr := do
  if (← hasSameType a b) then
    mkEqProof a b
  else
    mkHEqProof a b

/--
Returns a proof that `a = True`.
It assumes `a` and `True` are in the same equivalence class.
-/
def mkEqTrueProof (a : Expr) : GoalM Expr := do
  mkEqProof a (← getTrueExpr)

/--
Returns a proof that `a = False`.
It assumes `a` and `False` are in the same equivalence class.
-/
def mkEqFalseProof (a : Expr) : GoalM Expr := do
  mkEqProof a (← getFalseExpr)

/--
Returns a proof that `a = Bool.true`.
It assumes `a` and `Bool.true` are in the same equivalence class.
-/
def mkEqBoolTrueProof (a : Expr) : GoalM Expr := do
  mkEqProof a (← getBoolTrueExpr)

/--
Returns a proof that `a = Bool.false`.
It assumes `a` and `Bool.false` are in the same equivalence class.
-/
def mkEqBoolFalseProof (a : Expr) : GoalM Expr := do
  mkEqProof a (← getBoolFalseExpr)

/-- Marks current goal as inconsistent without assigning `mvarId`. -/
def markAsInconsistent : GoalM Unit := do
  unless (← get).inconsistent do
    trace[grind] "closed `{← (← get).mvarId.getTag}`"
    modify fun s => { s with inconsistent := true }

/--
Assign the `mvarId` using the given proof of `False`.
If type of `mvarId` is not `False`, then use `False.elim`.
-/
def _root_.Lean.MVarId.assignFalseProof (mvarId : MVarId) (falseProof : Expr) : MetaM Unit := mvarId.withContext do
  let target ← mvarId.getType
  if target.isFalse then
    /-
    **Note**: We add the marker to assist `getFalseExpr?` used to implement
    non-chronological backtracking. -/
    mvarId.assign (mkExpectedPropHint falseProof (mkConst ``False))
  else
    mvarId.assign (← mkFalseElim target falseProof)

/--
`goal.withContext x` executes `x` using the given metavariable `LocalContext` and `LocalInstances`.
The type class resolution cache is flushed when executing `x` if its `LocalInstances` are
different from the current ones. -/
@[inline] def Goal.withContext [MonadControlT MetaM m] [Monad m] (goal : Goal) : m α → m α :=
  goal.mvarId.withContext

/--
Creates an auxiliary metavariable with the same type and context of `goal.mvarId`.
We use this function to perform `cases` on the current goal without eagerly assigning it.
-/
def Goal.mkAuxMVar (goal : Goal) : MetaM MVarId := goal.withContext do
  let mvarId := goal.mvarId
  let tag ← mvarId.getTag
  let type ← mvarId.getType
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar type tag
  return mvarNew.mvarId!

/--
Closes the current goal using the given proof of `False` and
marks it as inconsistent if it is not already marked so.
-/
def closeGoal (falseProof : Expr) : GoalM Unit := do
  markAsInconsistent
  let mvarId := (← get).mvarId
  unless (← mvarId.isAssigned) do
    mvarId.assignFalseProof falseProof

/-- Returns all enodes in the goal -/
def getExprs : GoalM (PArray Expr) := do
  return (← get).exprs

/-- Executes `f` to each term in the equivalence class containing `e` -/
@[inline] def traverseEqc (e : Expr) (f : ENode → GoalM Unit) : GoalM Unit := do
  let mut curr := e
  repeat
    let n ← getENode curr
    f n
    if isSameExpr n.next e then return ()
    curr := n.next

/--
Executes `f` to each term in the equivalence class containing `e`, and stops as soon as `f` returns `true`.
-/
@[inline] def findEqc (e : Expr) (f : ENode → GoalM Bool) : GoalM Bool := do
  let mut curr := e
  repeat
    let n ← getENode curr
    if (← f n) then return true
    if isSameExpr n.next e then break
    curr := n.next
  return false

/-- Folds using `f` and `init` over the equivalence class containing `e` -/
@[inline] def foldEqc (e : Expr) (init : α) (f : ENode → α → GoalM α) : GoalM α := do
  let mut curr := e
  let mut r := init
  repeat
    let n ← getENode curr
    r ← f n r
    if isSameExpr n.next e then return r
    curr := n.next
  unreachable!
  return r

def forEachENode (f : ENode → GoalM Unit) : GoalM Unit := do
  for e in (← getExprs) do
    let n ← getENode e
    f n

def filterENodes (p : ENode → GoalM Bool) : GoalM (Array ENode) := do
  let ref ← IO.mkRef #[]
  forEachENode fun n => do
    if (← p n) then
      ref.modify (·.push n)
  ref.get

def forEachEqcRoot (f : ENode → GoalM Unit) : GoalM Unit := do
  for e in (← getExprs) do
    let n ← getENode e
    if n.isRoot then
      f n

abbrev Propagator := Expr → GoalM Unit
abbrev EvalTactic := Goal → TSyntax `grind → GrindM (List Goal)
def EvalTactic.skip : EvalTactic := fun goal _ => return [goal]

structure Methods where
  propagateUp   : Propagator := fun _ => return ()
  propagateDown : Propagator := fun _ => return ()
  evalTactic    : EvalTactic := EvalTactic.skip
  deriving Inhabited

def Methods.toMethodsRef (m : Methods) : MethodsRef :=
  unsafe unsafeCast m

private def MethodsRef.toMethods (m : MethodsRef) : Methods :=
  unsafe unsafeCast m

@[inline] def getMethods : GrindM Methods :=
  return (← getMethodsRef).toMethods

def propagateUp (e : Expr) : GoalM Unit := do
  (← getMethods).propagateUp e

def propagateDown (e : Expr) : GoalM Unit := do
  (← getMethods).propagateDown e

def evalTactic (goal : Goal) (stx : TSyntax `grind) : GrindM (List Goal) := do
  (← getMethods).evalTactic goal stx

/-- Returns expressions in the given expression equivalence class. -/
partial def Goal.getEqc (goal : Goal) (e : Expr) (sort := false) : List Expr :=
  let eqc := go e e #[]
  if sort then
    Array.toList <| eqc.qsort fun e₁ e₂ =>
      let g₁ := goal.getGeneration e₁
      let g₂ := goal.getGeneration e₂
      if g₁ != g₂ then g₁ < g₂ else e₁.lt e₂
  else
    eqc.toList
where
  go (first : Expr) (e : Expr) (acc : Array Expr) : Array Expr := Id.run do
    let some next := goal.getNext? e | acc
    let acc := acc.push e
    if isSameExpr first next then
      return acc
    else
      go first next acc

@[inline, inherit_doc Goal.getEqc]
partial def getEqc (e : Expr) (sort := false) : GoalM (List Expr) :=
  return (← get).getEqc e sort

/-- Returns all equivalence classes in the current goal. -/
partial def Goal.getEqcs (goal : Goal) (sort := false) : List (List Expr) := Id.run do
 let mut r : Array (Nat × Expr × List Expr) := #[]
 for e in goal.exprs do
    let some node := goal.getENode? e | pure ()
    if node.isRoot then
      let e :: es := goal.getEqc node.self sort | unreachable!
      r := r.push (goal.getGeneration e, e, es)
  if sort then
    r := r.qsort fun (g₁, e₁, _) (g₂, e₂, _) => if g₁ != g₂ then g₁ < g₂ else e₁.lt e₂
  return r.toList.map fun (_, e, es) => e::es

@[inline, inherit_doc Goal.getEqcs]
def getEqcs : GoalM (List (List Expr)) :=
  return (← get).getEqcs

/--
Returns `true` if `s` has been already added to the case-split list at one point.
Remark: this function returns `true` even if the split has already been resolved
and is not in the list anymore.
-/
def isKnownCaseSplit (s : SplitInfo) : GoalM Bool :=
  return (← get).split.added.contains s

/-- Returns `true` if `e` is a case-split that does not need to be performed anymore. -/
def isResolvedCaseSplit (e : Expr) : GoalM Bool :=
  return (← get).split.resolved.contains { expr := e }

/--
Marks `e` as a case-split that does not need to be performed anymore.
Remark: we currently use this feature to disable `match`-case-splits.
Remark: we also use this feature to record the case-splits that have already been performed.
-/
def markCaseSplitAsResolved (e : Expr) : GoalM Unit := do
  unless (← isResolvedCaseSplit e) do
    trace_goal[grind.split.resolved] "{e}"
    modify fun s => { s with split.resolved := s.split.resolved.insert { expr := e } }

private def updateSplitArgPosMap (sinfo : SplitInfo) : GoalM Unit := do
  let .arg a b i _ _ := sinfo | return ()
  let key := (a, b)
  let is := (← get).split.argPosMap[key]? |>.getD []
  modify fun s => { s with
    split.argPosMap := s.split.argPosMap.insert key (i :: is)
  }

/-- Inserts `e` into the list of case-split candidates if it was not inserted before. -/
def addSplitCandidate (sinfo : SplitInfo) : GoalM Unit := do
  unless (← isKnownCaseSplit sinfo) do
    trace_goal[grind.split.candidate] "{sinfo.getExpr}"
    modify fun s => { s with
      split.added := s.split.added.insert sinfo
      split.candidates := sinfo :: s.split.candidates
    }
    updateSplitArgPosMap sinfo

inductive ActivateNextGuardResult where
  | ready
  | next (guard : Expr) (pending : List TheoremGuard)

def activateNextGuard (thm : EMatchTheorem) (guards : List TheoremGuard) (generation : Nat) : GoalM ActivateNextGuardResult := do
  go guards
where
  go : List TheoremGuard → GoalM ActivateNextGuardResult
    | [] => return .ready
    | guard :: guards => do
      let { expr := e, .. } ← preprocess guard.e
      internalize e generation
      if (← isEqTrue e) then
        go guards
      else
        if guard.check then
          addSplitCandidate <| .default e (.guard thm.origin)
        return .next e guards

/-- Adds a new theorem instance produced using E-matching. -/
def addTheoremInstance (thm : EMatchTheorem) (proof : Expr) (prop : Expr) (generation : Nat) (guards : List TheoremGuard) : GoalM Unit := do
  match (← activateNextGuard thm guards generation) with
  | .ready =>
    trace_goal[grind.ematch.instance] "{thm.origin.pp}: {prop}"
    saveEMatchTheorem thm
    addNewRawFact proof prop generation (.ematch thm.origin)
    modify fun s => { s with ematch.numInstances := s.ematch.numInstances + 1 }
  | .next guard guards =>
    let thms := (← get).ematch.delayedThmInsts.find? { expr := guard } |>.getD []
    let thms := { thm, proof, prop, generation, guards } :: thms
    trace_goal[grind.ematch.instance.delayed] "`{thm.origin.pp}` waiting{indentExpr guard}"
    modify fun s => { s with
      ematch.delayedThmInsts := s.ematch.delayedThmInsts.insert { expr := guard } thms
      ematch.numDelayedInstances := s.ematch.numDelayedInstances + 1
    }

def DelayedTheoremInstance.check (delayed : DelayedTheoremInstance) : GoalM Unit := do
  addTheoremInstance delayed.thm delayed.proof delayed.prop delayed.generation delayed.guards

/--
Returns extensionality theorems for the given type if available.
If `Config.ext` is `false`, the result is `#[]`.
-/
def getExtTheorems (type : Expr) : GoalM (Array Ext.ExtTheorem) := do
  unless (← getConfig).ext || (← getConfig).extAll do return #[]
  if let some thms := (← get).extThms.find? { expr := type } then
    return thms
  else
    let thms ← Ext.getExtTheorems type
    let thms ← if (← getConfig).extAll then
      pure thms
    else
      thms.filterM fun thm => isExtTheorem thm.declName
    modify fun s => { s with extThms := s.extThms.insert { expr := type } thms }
    return thms

/-- Add a new lookahead candidate. -/
def addLookaheadCandidate (sinfo : SplitInfo) : GoalM Unit := do
  trace_goal[grind.lookahead.add] "{sinfo.getExpr}"
  modify fun s => { s with split.lookaheads := sinfo :: s.split.lookaheads }
  updateSplitArgPosMap sinfo

/--
Helper function for executing `x` with a fresh `newFacts` and without modifying
the goal state.
-/
def withoutModifyingState (x : GoalM α) : GoalM α := do
  let saved ← get
  modify fun goal => { goal with newFacts := {} }
  try
    x
  finally
    set saved

/-- Canonicalizes nested types, type formers, and instances in `e`. -/
@[extern "lean_grind_canon"] -- Forward definition
opaque canon (e : Expr) : GoalM Expr

/-!
`Action` is the *control interface* for `grind`’s search steps. It is defined in
Continuation-Passing Style (CPS).
See `Grind/Action.lean` for additional details.
-/

abbrev TGrind := TSyntax `grind

/-- Result type for a `grind` Action -/
inductive ActionResult where
  | /--
    The goal has been closed, and you can use `seq` to close the goal efficiently.
    -/
    closed (seq : List TGrind)
  | /--
    The action could not make further progress.
    `gs` are subgoals that could not be closed. They are used for producing error messages.
    -/
    stuck (gs : List Goal)
  deriving Inhabited

abbrev ActionCont : Type :=
  Goal → GrindM ActionResult

abbrev Action : Type :=
  Goal → (kna : ActionCont) → (kp : ActionCont) → GrindM ActionResult

@[expose] def Action.notApplicable : Action := fun goal kna _ =>
  kna goal

instance : Inhabited Action where
  default := Action.notApplicable

/-!
Solver Extensions
-/

/--
Solver extension, can only be generated by `registerSolverExtension` that allocates a unique index
for this extension into each goal's extension state's array.
-/
structure SolverExtension (σ : Type) where private mk ::
  id          : Nat
  mkInitial   : IO σ
  internalize : Expr → (parent? : Option Expr) → GoalM Unit
  newEq       : Expr → Expr → GoalM Unit
  newDiseq    : Expr → Expr → GoalM Unit
  mbtc        : GoalM Bool
  action      : Action
  check       : GoalM Bool -- **TODO**: Consider deleting `check` in the future.
  checkInv    : GoalM Unit
  deriving Inhabited

private builtin_initialize solverExtensionsRef : IO.Ref (Array (SolverExtension SolverExtensionState)) ← IO.mkRef #[]

/--
Registers a new solver extension for `grind`.
Solver extensions can only be registered during initialization.
Reason: We do not use any synchronization primitive to access `solverExtensionsRef`.
-/
def registerSolverExtension {σ : Type} (mkInitial : IO σ) : IO (SolverExtension σ) := do
  unless (← initializing) do
    throw (IO.userError "failed to register `grind` solver, extensions can only be registered during initialization")
  let exts ← solverExtensionsRef.get
  let id := exts.size
  let ext : SolverExtension σ := {
    id, mkInitial
    internalize := fun _ _ => return ()
    newEq := fun _ _ => return ()
    newDiseq := fun _ _ => return ()
    action := Action.notApplicable
    check := fun _ _ => return false
    checkInv := fun _ _ => return ()
    mbtc := fun _ _ => return false
  }
  solverExtensionsRef.modify fun exts => exts.push (unsafe unsafeCast ext)
  return ext

/--
Sets methods/handlers for solver extension `ext`.
Solver extension methods can only be registered during initialization.
Reason: We do not use any synchronization primitive to access `solverExtensionsRef`.
-/
def SolverExtension.setMethods (ext : SolverExtension σ)
    (internalize : Expr → (parent? : Option Expr) → GoalM Unit := fun _ _  => return ())
    (newEq       : Expr → Expr → GoalM Unit := fun _ _ => return ())
    (newDiseq    : Expr → Expr → GoalM Unit := fun _ _ => return ())
    (mbtc        : GoalM Bool := return false)
    (action      : Action := Action.notApplicable)
    (check       : GoalM Bool := return false)
    (checkInv    : GoalM Unit := return ())
    : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register `grind` solver, extensions can only be registered during initialization")
  unless ext.id < (← solverExtensionsRef.get).size do
    throw (IO.userError "failed to register `grind` solver methods, invalid solver id")
  solverExtensionsRef.modify fun exts => exts.modify ext.id fun s => { s with
    internalize, newEq, newDiseq, mbtc, action, check, checkInv
  }

/-- Returns initial state for registered solvers. -/
def Solvers.mkInitialStates : IO (Array SolverExtensionState) := do
  let exts ← solverExtensionsRef.get
  exts.mapM fun ext => ext.mkInitial

instance : Inhabited (GoalM σ) where
  default := throwError "<GoalM action default value>"

private unsafe def SolverExtension.modifyStateImpl (ext : SolverExtension σ) (f : σ → σ) : GoalM Unit := do
  modify fun s => { s with
    sstates := s.sstates.modify ext.id fun solverState => unsafeCast (f (unsafeCast solverState))
  }

@[implemented_by SolverExtension.modifyStateImpl]
opaque SolverExtension.modifyState (ext : SolverExtension σ) (f : σ → σ) : GoalM Unit

private unsafe def SolverExtension.getStateCoreImpl (ext : SolverExtension σ) (goal : Goal) : IO σ :=
  return unsafeCast goal.sstates[ext.id]!

@[implemented_by SolverExtension.getStateCoreImpl]
opaque SolverExtension.getStateCore (ext : SolverExtension σ) (goal : Goal) : IO σ

def SolverExtension.getState (ext : SolverExtension σ) : GoalM σ := do
  ext.getStateCore (← get)

/-- Internalizes given expression in all registered solvers. -/
def Solvers.internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  (← solverExtensionsRef.get).forM fun ext => ext.internalize e parent?

/-- Checks invariants of all registered solvers. -/
def Solvers.checkInvariants : GoalM Unit := do
  (← solverExtensionsRef.get).forM fun ext => ext.checkInv

/--
Performs (expensive) satisfiability checks in all registered solvers,
and returns the solver ids that made progress.
-/
def Solvers.check? : GoalM (Option (Array Nat)) := do
  let mut result := #[]
  for ext in (← solverExtensionsRef.get) do
    if (← isInconsistent) then
      return some result
    if (← ext.check) then
      result := result.push ext.id
  if !result.isEmpty then
    processNewFacts
    return some result
  else
    return none

def Solvers.check : GoalM Bool := do
  return !(← check?).isNone

/-- Invokes model-based theory combination extensions in all registered solvers. -/
def Solvers.mbtc : GoalM Bool := do
  let mut result := false
  for ext in (← solverExtensionsRef.get) do
    if (← ext.mbtc) then
      result := true
  return result

/--
Sequential conjunction: executes both `x` and `y`.

- Runs `x` and always runs `y` afterward, regardless of whether `x` made progress.
- It is not applicable only if both `x` and `y` are not applicable.
-/
def Action.andAlso (x y : Action) : Action := fun goal kna kp => do
  x goal (fun goal => y goal kna kp) (fun goal => y goal kp kp)

/-
Creates an action that tries all solver extensions. It uses the `Action.andAlso`
to combine them.
-/
def Solvers.mkAction : IO Action := do
  let exts ← solverExtensionsRef.get
  let rec go (i : Nat) (acc : Action) : Action :=
    if h : i < exts.size then
      go (i+1) (acc.andAlso exts[i].action)
    else
      acc
  if h : 0 < exts.size then
    return go 1 exts[0].action
  else
    return Action.notApplicable

/--
Given a new disequality `lhs ≠ rhs`, propagates it to relevant theories.
-/
def Solvers.propagateDiseqs (lhs rhs : Expr) : GoalM Unit := do
  go (← getRootENode lhs).sTerms (← getRootENode rhs).sTerms
where
  go (lhsTerms rhsTerms : SolverTerms) : GoalM Unit := do
    match lhsTerms, rhsTerms with
    | .nil, _ => return ()
    | _, .nil => return ()
    | .next id₁ lhs lhsTerms, .next id₂ rhs rhsTerms =>
      if id₁ == id₂ then
        (← solverExtensionsRef.get)[id₁]!.newDiseq lhs rhs
        go lhsTerms rhsTerms
      else if id₁ < id₂ then
        go lhsTerms (.next id₂ rhs rhsTerms)
      else
        go (.next id₁ lhs lhsTerms) rhsTerms

private def propagateDiseqOf (id : Nat) (lhs rhs : Expr) : GoalM Unit := do
  visitLhs (← getRootENode lhs).sTerms
where
  visitLhs (sTerms : SolverTerms) : GoalM Unit := do
    match sTerms with
    | .nil => return ()
    | .next id' e sTerms =>
      if id == id' then
        visitRhs e (← getRootENode rhs).sTerms
      else if id < id' then
        return ()
      else
        visitLhs sTerms

  visitRhs (lhsTerm : Expr) (sTerms : SolverTerms) : GoalM Unit := do
    match sTerms with
    | .nil => return ()
    | .next id' e sTerms =>
      if id == id' then
        let rhsTerm := e
        (← solverExtensionsRef.get)[id]!.newDiseq lhsTerm rhsTerm
      else if id < id' then
        return ()
      else
        visitRhs lhsTerm sTerms

def isSameSolverTerms (a b : SolverTerms) : Bool :=
  unsafe ptrEq a b

def SolverExtension.markTerm (ext : SolverExtension σ) (e : Expr) : GoalM Unit := do
  let root ← getRootENode e
  let id := ext.id
  let rec go (sTerms : SolverTerms) : GoalM SolverTerms := do
    match sTerms with
    | .nil => return .next id e .nil
    | .next id' e' sTerms' =>
      if id == id' then
        (← solverExtensionsRef.get)[id]!.newEq e e'
        return sTerms
      else if id < id' then
        return .next id e sTerms
      else
        let sTermsNew ← go sTerms'
        if isSameSolverTerms sTermsNew sTerms' then
          return sTerms
        else
          return .next id' e' sTermsNew
  let sTermsNew ← go root.sTerms
  unless isSameSolverTerms sTermsNew root.sTerms do
    setENode root.self { root with sTerms := sTermsNew }
    forEachDiseq (← getParents root.self) (propagateDiseqOf id)

/--
Returns `some t` if `t` is the solver term for `ext` associated with `e`.
-/
def SolverExtension.getTerm (ext : SolverExtension σ) (e : ENode) : Option Expr :=
  go ext.id e.sTerms
where
  go (solverId : Nat) : SolverTerms → Option Expr
    | .nil => none
    | .next id t rest => if id == solverId then some t else go solverId rest

/--
Returns `true` if the root of `e`s equivalence class is already attached to a term
of the given solver.
-/
def SolverExtension.hasTermAtRoot (ext : SolverExtension σ) (e : Expr) : GoalM Bool := do
  return go ext.id (← getRootENode e).sTerms
where
  go (solverId : Nat) : SolverTerms → Bool
    | .nil => false
    | .next id _ rest => id == solverId || go solverId rest

private inductive PendingSolverPropagationsData where
  | nil
  | eq (solverId : Nat) (lhs rhs : Expr) (rest : PendingSolverPropagationsData)
  | diseqs (solverId : Nat) (ps : ParentSet) (rest : PendingSolverPropagationsData)

structure PendingSolverPropagations where private mk ::
  private data : PendingSolverPropagationsData

def Solvers.mergeTerms (rhsRoot lhsRoot : ENode) : GoalM PendingSolverPropagations := do
  let (sTerms, data) ← go rhsRoot.sTerms lhsRoot.sTerms
  unless sTerms matches .nil do
    -- We have to retrieve the node because other fields have been updated
    let rhsRoot ← getENode rhsRoot.self
    setENode rhsRoot.self { rhsRoot with sTerms }
  return { data }
where
  toPendingDiseqs (sTerms : SolverTerms) (ps : ParentSet) : PendingSolverPropagationsData :=
    match sTerms with
    | .nil => .nil
    | .next id _ sTerms => .diseqs id ps (toPendingDiseqs sTerms ps)

  go (rhsTerms : SolverTerms) (lhsTerms : SolverTerms) : GoalM (SolverTerms × PendingSolverPropagationsData) := do
    match rhsTerms, lhsTerms with
    | .nil,     .nil     => return (.nil, .nil)
    | .nil,     .next .. => return (lhsTerms, toPendingDiseqs lhsTerms (← getParents rhsRoot.self))
    | .next .., .nil     => return (rhsTerms, toPendingDiseqs rhsTerms (← getParents lhsRoot.self))
    | .next id₁ rhs rhsTerms, .next id₂ lhs lhsTerms =>
      if id₁ == id₂ then
        let (s, p) ← go rhsTerms lhsTerms
        return (.next id₁ rhs s, .eq id₁ lhs rhs p)
      else if id₁ < id₂ then
        let (s, p) ← go rhsTerms (.next id₂ lhs lhsTerms)
        return (.next id₁ rhs s, .diseqs id₁ (← getParents lhsRoot.self) p)
      else
        let (s, p) ← go (.next id₁ rhs rhsTerms) lhsTerms
        return (.next id₂ lhs s, .diseqs id₂ (← getParents rhsRoot.self) p)

def PendingSolverPropagations.propagate (p : PendingSolverPropagations) : GoalM Unit := do
  go p.data
where
  go (p : PendingSolverPropagationsData) : GoalM Unit := do
    match p with
    | .nil => return ()
    | .eq solverId lhs rhs rest =>
      (← solverExtensionsRef.get)[solverId]!.newEq lhs rhs
      go rest
    | .diseqs solverId parentSet rest =>
      forEachDiseq parentSet (propagateDiseqOf solverId)
      go rest

def anchorPrefixToString (numDigits : Nat) (anchorPrefix : UInt64) : String :=
  let cs := Nat.toDigits 16 anchorPrefix.toNat
  let n := cs.length
  let zs := List.replicate (numDigits - n) '0'
  let cs := zs ++ cs
  String.ofList cs

def anchorToString (numDigits : Nat) (anchor : UInt64) : String :=
  anchorPrefixToString numDigits (anchor >>> (64 - 4*numDigits.toUInt64))

def AnchorRef.toString (anchorRef : AnchorRef) : String :=
  anchorPrefixToString anchorRef.numDigits anchorRef.anchorPrefix

instance : ToString AnchorRef where
  toString := AnchorRef.toString

/--
Returns activated `match`-declaration equations.
Recall that in tactics such as `instantiate only [...]`, `match`-declarations are always instantiated.
-/
def Goal.getActiveMatchEqTheorems (goal : Goal) : CoreM (Array EMatchTheorem) := do
  let k (thms : Array EMatchTheorem) (thm : EMatchTheorem) : CoreM (Array EMatchTheorem) := do
    if (← isMatchEqLikeDeclName thm.origin.key) then
      return thms.push thm
    else
      return thms
  let result ← goal.ematch.newThms.foldlM k #[]
  goal.ematch.thms.foldlM k result

end Lean.Meta.Grind
