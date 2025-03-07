/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Tactics
import Init.Data.Queue
import Std.Data.TreeSet
import Lean.Util.ShareCommon
import Lean.HeadIndex
import Lean.Meta.Basic
import Lean.Meta.CongrTheorems
import Lean.Meta.AbstractNestedProofs
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Ext
import Lean.Meta.Tactic.Grind.ENodeKey
import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.Cases
import Lean.Meta.Tactic.Grind.Arith.Types
import Lean.Meta.Tactic.Grind.EMatchTheorem

namespace Lean.Meta.Grind

/-- We use this auxiliary constant to mark delayed congruence proofs. -/
def congrPlaceholderProof := mkConst (Name.mkSimple "[congruence]")

/--
Returns `true` if `e` is `True`, `False`, or a literal value.
See `Lean.Meta.LitValues` for supported literals.
-/
def isInterpreted (e : Expr) : MetaM Bool := do
  if e.isTrue || e.isFalse then return true
  isLitValue e

register_builtin_option grind.debug : Bool := {
  defValue := false
  group    := "debug"
  descr    := "check invariants after updates"
}

register_builtin_option grind.debug.proofs : Bool := {
  defValue := false
  group    := "debug"
  descr    := "check proofs between the elements of all equivalence classes"
}

register_builtin_option grind.warning : Bool := {
  defValue := true
  group    := "debug"
  descr    := "disable `grind` usage warning"
}

/-- Context for `GrindM` monad. -/
structure Context where
  simp         : Simp.Context
  simprocs     : Array Simp.Simprocs
  mainDeclName : Name
  config       : Grind.Config

/-- Key for the congruence theorem cache. -/
structure CongrTheoremCacheKey where
  f       : Expr
  numArgs : Nat

-- We manually define `BEq` because we want to use pointer equality.
instance : BEq CongrTheoremCacheKey where
  beq a b := isSameExpr a.f b.f && a.numArgs == b.numArgs

-- We manually define `Hashable` because we want to use pointer equality.
instance : Hashable CongrTheoremCacheKey where
  hash a := mixHash (unsafe ptrAddrUnsafe a.f).toUInt64 (hash a.numArgs)

structure EMatchTheoremTrace where
  origin : Origin
  kind   : EMatchTheoremKind
  deriving BEq, Hashable

/--
E-match theorems and case-splits performed by `grind`.
Note that it may contain elements that are not needed by the final proof.
For example, `grind` instantiated the theorem, but theorem instance was not actually used
in the proof.
-/
structure Trace where
  thms       : PHashSet EMatchTheoremTrace := {}
  eagerCases : PHashSet Name := {}
  cases      : PHashSet Name := {}
  deriving Inhabited

structure Counters where
  /-- Number of times E-match theorem has been instantiated. -/
  thm  : PHashMap Origin Nat := {}
  /-- Number of times a `cases` has been performed on an inductive type/predicate -/
  case : PHashMap Name Nat := {}
  deriving Inhabited

private def emptySC : ShareCommon.State.{0} ShareCommon.objectFactory := ShareCommon.State.mk _

/-- State for the `GrindM` monad. -/
structure State where
  /-- `ShareCommon` (aka `Hashconsing`) state. -/
  scState    : ShareCommon.State.{0} ShareCommon.objectFactory := emptySC
  /-- Next index for creating auxiliary theorems. -/
  nextThmIdx : Nat := 1
  /--
  Congruence theorems generated so far. Recall that for constant symbols
  we rely on the reserved name feature (i.e., `mkHCongrWithArityForConst?`).
  Remark: we currently do not reuse congruence theorems
  -/
  congrThms  : PHashMap CongrTheoremCacheKey CongrTheorem := {}
  simpStats  : Simp.Stats := {}
  trueExpr   : Expr
  falseExpr  : Expr
  natZExpr   : Expr
  btrueExpr  : Expr
  bfalseExpr : Expr
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
  /-- `trace` for `grind?` -/
  trace      : Trace := {}
  /-- Performance counters -/
  counters   : Counters := {}

private opaque MethodsRefPointed : NonemptyType.{0}
private def MethodsRef : Type := MethodsRefPointed.type
instance : Nonempty MethodsRef := MethodsRefPointed.property

abbrev GrindM := ReaderT MethodsRef $ ReaderT Context $ StateRefT State MetaM

/-- Returns the user-defined configuration options -/
def getConfig : GrindM Grind.Config :=
  return (← readThe Context).config

/-- Returns the internalized `True` constant.  -/
def getTrueExpr : GrindM Expr := do
  return (← get).trueExpr

/-- Returns the internalized `False` constant.  -/
def getFalseExpr : GrindM Expr := do
  return (← get).falseExpr

/-- Returns the internalized `Bool.true`.  -/
def getBoolTrueExpr : GrindM Expr := do
  return (← get).btrueExpr

/-- Returns the internalized `Bool.false`.  -/
def getBoolFalseExpr : GrindM Expr := do
  return (← get).bfalseExpr

/-- Returns the internalized `0 : Nat` numeral.  -/
def getNatZeroExpr : GrindM Expr := do
  return (← get).natZExpr

def getMainDeclName : GrindM Name :=
  return (← readThe Context).mainDeclName

def saveEMatchTheorem (thm : EMatchTheorem) : GrindM Unit := do
  if (← getConfig).trace then
    modify fun s => { s with trace.thms := s.trace.thms.insert { origin := thm.origin, kind := thm.kind } }
  modify fun s => { s with
    counters.thm := if let some n := s.counters.thm.find? thm.origin then
      s.counters.thm.insert thm.origin (n+1)
    else
      s.counters.thm.insert thm.origin 1
  }

def saveCases (declName : Name) (eager : Bool) : GrindM Unit := do
  if (← getConfig).trace then
    if eager then
      modify fun s => { s with trace.eagerCases := s.trace.eagerCases.insert declName }
    else
      modify fun s => { s with trace.cases := s.trace.cases.insert declName }
  modify fun s => { s with
    counters.case := if let some n := s.counters.case.find? declName then
      s.counters.case.insert declName (n+1)
    else
      s.counters.case.insert declName 1
  }

@[inline] def getMethodsRef : GrindM MethodsRef :=
  read

/-- Returns maximum term generation that is considered during ematching. -/
def getMaxGeneration : GrindM Nat := do
  return (← getConfig).gen

/--
Abtracts nested proofs in `e`. This is a preprocessing step performed before internalization.
-/
def abstractNestedProofs (e : Expr) : GrindM Expr := do
  let nextIdx := (← get).nextThmIdx
  let (e, s') ← AbstractNestedProofs.visit e |>.run { baseName := (← getMainDeclName) } |>.run |>.run { nextIdx }
  modify fun s => { s with nextThmIdx := s'.nextIdx }
  return e

/--
Applies hash-consing to `e`. Recall that all expressions in a `grind` goal have
been hash-consed. We perform this step before we internalize expressions.
-/
def shareCommon (e : Expr) : GrindM Expr := do
  let scState ← modifyGet fun s => (s.scState, { s with scState := emptySC })
  let (e, scState) := ShareCommon.State.shareCommon scState e
  modify fun s => { s with scState }
  return e

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
    if let some result ← mkHCongrWithArityForConst? declName us numArgs then
      modify fun s => { s with congrThms := s.congrThms.insert key result }
      return result
  let result ← Meta.mkHCongrWithArity f numArgs
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

private def expandReportIssueMacro (s : Syntax) : MacroM (TSyntax `doElem) := do
  let msg ← if s.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| do
    if (← getConfig).verbose then
      reportIssue $msg)

macro "reportIssue!" s:(interpolatedStr(term) <|> term) : doElem => do
  expandReportIssueMacro s.raw

/--
Stores information for a node in the egraph.
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
  /--
  The `offset?` field is used to propagate equalities from the `grind` congruence closure module
  to the offset constraints module. When `grind` merges two equivalence classes, and both have
  an associated `offset?` set to `some e`, the equality is propagated. This field is
  assigned during the internalization of offset terms.
  -/
  offset? : Option Expr := none
  /--
  The `cutsat?` field is used to propagate equalities from the `grind` congruence closure module
  to the cutsat module. Its implementation is similar to the `offset?` field.
  -/
  cutsat? : Option Expr := none
  -- Remark: we expect to have builtin support for offset constraints, cutsat, and comm ring.
  -- If the number of satellite solvers increases, we may add support for an arbitrary solvers like done in Z3.
  deriving Inhabited, Repr

def ENode.isCongrRoot (n : ENode) :=
  isSameExpr n.self n.congr

/-- New equality to be processed. -/
structure NewEq where
  lhs   : Expr
  rhs   : Expr
  proof : Expr
  isHEq : Bool

abbrev ENodeMap := PHashMap ENodeKey ENode

/--
Key for the congruence table.
We need access to the `enodes` to be able to retrieve the equivalence class roots.
-/
structure CongrKey (enodes : ENodeMap) where
  e : Expr

private def hashRoot (enodes : ENodeMap) (e : Expr) : UInt64 :=
  if let some node := enodes.find? { expr := e } then
    unsafe (ptrAddrUnsafe node.root).toUInt64
  else
    13

def hasSameRoot (enodes : ENodeMap) (a b : Expr) : Bool := Id.run do
  if isSameExpr a b then
    return true
  else
    let some n1 := enodes.find? { expr := a } | return false
    let some n2 := enodes.find? { expr := b } | return false
    isSameExpr n1.root n2.root

def congrHash (enodes : ENodeMap) (e : Expr) : UInt64 :=
  match_expr e with
  | Grind.nestedProof p _ => hashRoot enodes p
  | Eq _ lhs rhs => goEq lhs rhs
  | _ => go e 17
where
  goEq (lhs rhs : Expr) : UInt64 :=
    let h₁ := hashRoot enodes lhs
    let h₂ := hashRoot enodes rhs
    if h₁ > h₂ then mixHash h₂ h₁ else mixHash h₁ h₂
  go (e : Expr) (r : UInt64) : UInt64 :=
    match e with
    | .app f a => go f (mixHash r (hashRoot enodes a))
    | _ => mixHash r (hashRoot enodes e)

/-- Returns `true` if `a` and `b` are congruent modulo the equivalence classes in `enodes`. -/
partial def isCongruent (enodes : ENodeMap) (a b : Expr) : Bool :=
  match_expr a with
  | Grind.nestedProof p₁ _ =>
    let_expr Grind.nestedProof p₂ _ := b | false
    hasSameRoot enodes p₁ p₂
  | Eq α₁ lhs₁ rhs₁ =>
    let_expr Eq α₂ lhs₂ rhs₂ := b | false
    if isSameExpr α₁ α₂ then
      goEq lhs₁ rhs₁ lhs₂ rhs₂
    else
      go a b
  | _ => go a b
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

instance : Hashable (CongrKey enodes) where
  hash k := congrHash enodes k.e

instance : BEq (CongrKey enodes) where
  beq k1 k2 := isCongruent enodes k1.e k2.e

abbrev CongrTable (enodes : ENodeMap) := PHashSet (CongrKey enodes)

-- Remark: we cannot use pointer addresses here because we have to traverse the tree.
abbrev ParentSet := Std.TreeSet Expr Expr.quickComp
abbrev ParentMap := PHashMap ENodeKey ParentSet

/--
The E-matching module instantiates theorems using the `EMatchTheorem proof` and a (partial) assignment.
We want to avoid instantiating the same theorem with the same assignment more than once.
Therefore, we store the (pre-)instance information in set.
Recall that the proofs of activated theorems have been hash-consed.
The assignment contains internalized expressions, which have also been hash-consed.
-/
structure PreInstance where
  proof      : Expr
  assignment : Array Expr

instance : Hashable PreInstance where
  hash i := Id.run do
    let mut r := unsafe (ptrAddrUnsafe i.proof >>> 3).toUInt64
    for v in i.assignment do
      r := mixHash r (unsafe (ptrAddrUnsafe v >>> 3).toUInt64)
    return r

instance : BEq PreInstance where
  beq i₁ i₂ := Id.run do
    unless isSameExpr i₁.proof i₂.proof do return false
    unless i₁.assignment.size == i₂.assignment.size do return false
    for v₁ in i₁.assignment, v₂ in i₂.assignment do
      unless isSameExpr v₁ v₂ do return false
    return true

abbrev PreInstanceSet := PHashSet PreInstance

/-- New fact to be processed. -/
structure NewFact where
  proof      : Expr
  prop       : Expr
  generation : Nat
  deriving Inhabited

/-- Canonicalizer state. See `Canon.lean` for additional details. -/
structure Canon.State where
  argMap     : PHashMap (Expr × Nat) (List (Expr × Expr)) := {}
  canon      : PHashMap Expr Expr := {}
  proofCanon : PHashMap Expr Expr := {}
  deriving Inhabited

/-- Trace information for a case split. -/
structure CaseTrace where
  expr : Expr
  i    : Nat
  num  : Nat
  deriving Inhabited

/-- E-matching related fields for the `grind` goal. -/
structure EMatch.State where
  /--
  Inactive global theorems. As we internalize terms, we activate theorems as we find their symbols.
  Local theorem provided by users are added directly into `newThms`.
  -/
  thmMap       : EMatchTheorems
  /-- Goal modification time. -/
  gmt          : Nat := 0
  /-- Active theorems that we have performed ematching at least once. -/
  thms         : PArray EMatchTheorem := {}
  /-- Active theorems that we have not performed any round of ematching yet. -/
  newThms      : PArray EMatchTheorem := {}
  /-- Number of theorem instances generated so far -/
  numInstances : Nat := 0
  /-- Number of E-matching rounds performed in this goal since the last case-split. -/
  num          : Nat := 0
  /-- (pre-)instances found so far. It includes instances that failed to be instantiated. -/
  preInstances : PreInstanceSet := {}
  /-- Next local E-match theorem idx. -/
  nextThmIdx   : Nat := 0
  /-- `match` auxiliary functions whose equations have already been created and activated. -/
  matchEqNames : PHashSet Name := {}
  deriving Inhabited

/-- Case splitting related fields for the `grind` goal. -/
structure Split.State where
  /-- Inductive datatypes marked for case-splitting -/
  casesTypes : CasesTypes := {}
  /-- Case-split candidates. -/
  candidates : List Expr := []
  /-- Number of splits performed to get to this goal. -/
  num        : Nat := 0
  /-- Case-splits that have already been performed, or that do not have to be performed anymore. -/
  resolved   : PHashSet ENodeKey := {}
  /--
  Sequence of cases steps that generated this goal. We only use this information for diagnostics.
  Remark: `casesTrace.length ≥ numSplits` because we don't increase the counter for `cases`
  applications that generated only 1 subgoal.
  -/
  trace      : List CaseTrace := []
  deriving Inhabited

/-- Clean name generator. -/
structure Clean.State where
  used : PHashSet Name := {}
  next : PHashMap Name Nat := {}
  deriving Inhabited

/-- The `grind` goal. -/
structure Goal where
  mvarId       : MVarId
  canon        : Canon.State := {}
  enodes       : ENodeMap := {}
  parents      : ParentMap := {}
  congrTable   : CongrTable enodes := {}
  /--
  A mapping from each function application index (`HeadIndex`) to a list of applications with that index.
  Recall that the `HeadIndex` for a constant is its constant name, and for a free variable,
  it is its unique id.
  -/
  appMap       : PHashMap HeadIndex (List Expr) := {}
  /-- Equations to be processed. -/
  newEqs       : Array NewEq := #[]
  /-- `inconsistent := true` if `ENode`s for `True` and `False` are in the same equivalence class. -/
  inconsistent : Bool := false
  /-- Next unique index for creating ENodes -/
  nextIdx      : Nat := 0
  /-- new facts to be processed. -/
  newFacts     : Std.Queue NewFact := ∅
  /-- Asserted facts -/
  facts      : PArray Expr := {}
  /-- Cached extensionality theorems for types. -/
  extThms    : PHashMap ENodeKey (Array Ext.ExtTheorem) := {}
  /-- State of the E-matching module. -/
  ematch     : EMatch.State
  /-- State of the case-splitting module. -/
  split      : Split.State := {}
  /-- State of arithmetic procedures. -/
  arith      : Arith.State := {}
  /-- State of the clean name generator. -/
  clean      : Clean.State := {}
  deriving Inhabited

def Goal.admit (goal : Goal) : MetaM Unit :=
  goal.mvarId.admit

abbrev GoalM := StateRefT Goal GrindM

@[inline] def GoalM.run (goal : Goal) (x : GoalM α) : GrindM (α × Goal) :=
  goal.mvarId.withContext do StateRefT'.run x goal

@[inline] def GoalM.run' (goal : Goal) (x : GoalM Unit) : GrindM Goal :=
  goal.mvarId.withContext do StateRefT'.run' (x *> get) goal

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

/-- Adds a new fact `prop` with proof `proof` to the queue for processing. -/
def addNewFact (proof : Expr) (prop : Expr) (generation : Nat) : GoalM Unit := do
  if grind.debug.get (← getOptions) then
    unless (← withReducible <| isDefEq (← inferType proof) prop) do
      throwError "`grind` internal error, trying to assert{indentExpr prop}\n\
        with proof{indentExpr proof}\nwhich has type{indentExpr (← inferType proof)}\n\
        which is not definitionally equal with `reducible` transparency setting}"
  modify fun s => { s with newFacts := s.newFacts.enqueue { proof, prop, generation } }

/-- Adds a new theorem instance produced using E-matching. -/
def addTheoremInstance (thm : EMatchTheorem) (proof : Expr) (prop : Expr) (generation : Nat) : GoalM Unit := do
  saveEMatchTheorem thm
  addNewFact proof prop generation
  modify fun s => { s with ematch.numInstances := s.ematch.numInstances + 1 }

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
  goal.enodes.find? { expr := e }

@[inline, inherit_doc Goal.getENode?]
def getENode? (e : Expr) : GoalM (Option ENode) :=
  return (← get).getENode? e

def throwNonInternalizedExpr (e : Expr) : CoreM α :=
  throwError "internal `grind` error, term has not been internalized{indentExpr e}"

/-- Returns node associated with `e`. It assumes `e` has already been internalized. -/
def Goal.getENode (goal : Goal) (e : Expr) : CoreM ENode := do
  let some n := goal.enodes.find? { expr := e }
    | throwNonInternalizedExpr e
  return n

@[inline, inherit_doc Goal.getENode]
def getENode (e : Expr) : GoalM ENode := do
  (← get).getENode e

/-- Returns the generation of the given term. Is assumes it has been internalized -/
def getGeneration (e : Expr) : GoalM Nat := do
  let some n ← getENode? e | return 0
  return n.generation

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
def Goal.getRoot (goal : Goal) (e : Expr) : CoreM Expr :=
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
Returns the next element in the equivalence class of `e`
if `e` has been internalized in the given goal.
-/
def Goal.getNext? (goal : Goal) (e : Expr) : Option Expr := Id.run do
  let some n ← goal.getENode? e | return none
  return some n.next

/-- Returns the next element in the equivalence class of `e`. -/
def Goal.getNext (goal : Goal) (e : Expr) : CoreM Expr :=
  return (← goal.getENode e).next

@[inline, inherit_doc Goal.getRoot]
def getNext (e : Expr) : GoalM Expr := do
  (← get).getNext e

/-- Returns `true` if `e` has already been internalized. -/
def alreadyInternalized (e : Expr) : GoalM Bool :=
  return (← get).enodes.contains { expr := e }

def Goal.getTarget? (goal : Goal) (e : Expr) : Option Expr := Id.run do
  let some n ← goal.getENode? e | return none
  return n.target?

@[inline] def getTarget? (e : Expr) : GoalM (Option Expr) := do
  return (← get).getTarget? e

/--
If `isHEq` is `false`, it pushes `lhs = rhs` with `proof` to `newEqs`.
Otherwise, it pushes `HEq lhs rhs`.
-/
def pushEqCore (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  if grind.debug.get (← getOptions) then
    unless proof == congrPlaceholderProof do
      let expectedType ← if isHEq then mkHEq lhs rhs else mkEq lhs rhs
      unless (← withReducible <| isDefEq (← inferType proof) expectedType) do
        throwError "`grind` internal error, trying to assert equality{indentExpr expectedType}\n\
            with proof{indentExpr proof}\nwhich has type{indentExpr (← inferType proof)}\n\
            which is not definitionally equal with `reducible` transparency setting}"
      trace[grind.debug] "pushEqCore: {expectedType}"
  modify fun s => { s with newEqs := s.newEqs.push { lhs, rhs, proof, isHEq } }

/-- Return `true` if `a` and `b` have the same type. -/
def hasSameType (a b : Expr) : MetaM Bool :=
  withDefault do isDefEq (← inferType a) (← inferType b)

@[inline] def pushEqHEq (lhs rhs proof : Expr) : GoalM Unit := do
  if (← hasSameType lhs rhs) then
    pushEqCore lhs rhs proof (isHEq := false)
  else
    pushEqCore lhs rhs proof (isHEq := true)

/-- Pushes `lhs = rhs` with `proof` to `newEqs`. -/
@[inline] def pushEq (lhs rhs proof : Expr) : GoalM Unit :=
  pushEqCore lhs rhs proof (isHEq := false)

/-- Pushes `HEq lhs rhs` with `proof` to `newEqs`. -/
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
  for parent in parents do
    curr := curr.insert parent
  modify fun s => { s with parents := s.parents.insert { expr := root } curr }

def setENode (e : Expr) (n : ENode) : GoalM Unit :=
  modify fun s => { s with
    enodes := s.enodes.insert { expr := e } n
    congrTable := unsafe unsafeCast s.congrTable
  }

def mkENodeCore (e : Expr) (interpreted ctor : Bool) (generation : Nat) : GoalM Unit := do
  setENode e {
    self := e, next := e, root := e, congr := e, size := 1
    flipped := false
    heqProofs := false
    hasLambdas := e.isLambda
    mt := (← get).ematch.gmt
    idx := (← get).nextIdx
    interpreted, ctor, generation
  }
  modify fun s => { s with nextIdx := s.nextIdx + 1 }

/--
Creates an `ENode` for `e` if one does not already exist.
This method assumes `e` has been hashconsed.
-/
def mkENode (e : Expr) (generation : Nat) : GoalM Unit := do
  if (← alreadyInternalized e) then return ()
  let ctor := (← isConstructorAppCore? e).isSome
  let interpreted ← isInterpreted e
  mkENodeCore e interpreted ctor generation

/--
Notifies the offset constraint module that `a = b` where
`a` and `b` are terms that have been internalized by this module.
-/
@[extern "lean_process_new_offset_eq"] -- forward definition
opaque Arith.Offset.processNewEq (a b : Expr) : GoalM Unit

/--
Notifies the offset constraint module that `a = k` where
`a` is term that has been internalized by this module,
and `k` is a numeral.
-/
@[extern "lean_process_new_offset_eq_lit"] -- forward definition
opaque Arith.Offset.processNewEqLit (a k : Expr) : GoalM Unit

/-- Returns `true` if `e` is a numeral and has type `Nat`. -/
def isNatNum (e : Expr) : Bool := Id.run do
  let_expr OfNat.ofNat _ _ inst := e | false
  let_expr instOfNatNat _ := inst | false
  true

/--
Marks `e` as a term of interest to the offset constraint module.
If the root of `e`s equivalence class has already a term of interest,
a new equality is propagated to the offset module.
-/
def markAsOffsetTerm (e : Expr) : GoalM Unit := do
  let root ← getRootENode e
  if let some e' := root.offset? then
    Arith.Offset.processNewEq e e'
  else if isNatNum root.self && !isSameExpr e root.self then
    Arith.Offset.processNewEqLit e root.self
  else
    setENode root.self { root with offset? := some e }

/--
Notifies the cutsat module that `a = b` where
`a` and `b` are terms that have been internalized by this module.
-/
@[extern "lean_process_cutsat_eq"] -- forward definition
opaque Arith.Cutsat.processNewEq (a b : Expr) : GoalM Unit

/--
Notifies the cutsat module that `a = k` where
`a` is term that has been internalized by this module, and `k` is a numeral.
-/
@[extern "lean_process_cutsat_eq_lit"] -- forward definition
opaque Arith.Cutsat.processNewEqLit (a k : Expr) : GoalM Unit

/--
Notifies the cutsat module that `a ≠ b` where
`a` and `b` are terms that have been internalized by this module.
-/
@[extern "lean_process_cutsat_diseq"] -- forward definition
opaque Arith.Cutsat.processNewDiseq (a b : Expr) : GoalM Unit

/-- Returns `true` if `e` is a nonegative numeral and has type `Int`. -/
def isNonnegIntNum (e : Expr) : Bool := Id.run do
  let_expr OfNat.ofNat _ _ inst := e | false
  let_expr instOfNat _ := inst | false
  true

/-- Returns `true` if `e` is a numeral and has type `Int`. -/
def isIntNum (e : Expr) : Bool :=
  match_expr e with
  | Neg.neg _ inst e => Id.run do
    let_expr Int.instNegInt := inst | false
    isNonnegIntNum e
  | _ => isNonnegIntNum e

/--
Returns `true` if type of `t` is definitionally equal to `α`
-/
def hasType (t α : Expr) : MetaM Bool :=
  withDefault do isDefEq (← inferType t) α

/--
For each equality `b = c` in `parents`, executes `k b c` IF
- `b = c` is equal to `False`, and
-/
@[inline] def forEachDiseq (parents : ParentSet) (k : (lhs : Expr) → (rhs : Expr) → GoalM Unit) : GoalM Unit := do
  for parent in parents do
    let_expr Eq _ b c := parent | continue
    if (← isEqFalse parent) then
      k b c

/--
Given `lhs` and `rhs` that are known to be disequal, checks whether
`lhs` and `rhs` have cutsat terms `e₁` and `e₂` attached to them,
and invokes process `Arith.Cutsat.processNewDiseq e₁ e₂`
-/
def propagateCutsatDiseq (lhs rhs : Expr) : GoalM Unit := do
  let some lhs ← get? lhs | return ()
  let some rhs ← get? rhs | return ()
  -- Recall that core can take care of disequalities of the form `1≠2`.
  unless isIntNum lhs && isIntNum rhs do
    Arith.Cutsat.processNewDiseq lhs rhs
where
  get? (a : Expr) : GoalM (Option Expr) := do
    let root ← getRootENode a
    if isIntNum root.self then
      return some root.self
    return root.cutsat?

/--
Traverses disequalities in `parents`, and propagate the ones relevant to the
cutsat module.
-/
def propagateCutsatDiseqs (parents : ParentSet) : GoalM Unit := do
  forEachDiseq parents propagateCutsatDiseq

/--
Marks `e` as a term of interest to the cutsat module.
If the root of `e`s equivalence class has already a term of interest,
a new equality is propagated to the cutsat module.
-/
def markAsCutsatTerm (e : Expr) : GoalM Unit := do
  let root ← getRootENode e
  if let some e' := root.cutsat? then
    Arith.Cutsat.processNewEq e e'
  else if isIntNum root.self && !isSameExpr e root.self then
    Arith.Cutsat.processNewEqLit e root.self
  else
    setENode root.self { root with cutsat? := some e }
    propagateCutsatDiseqs (← getParents root.self)

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
Returns a proof that `HEq a b`.
It assumes `a` and `b` are in the same equivalence class.
-/
-- Forward definition
@[extern "lean_grind_mk_heq_proof"]
opaque mkHEqProof (a b : Expr) : GoalM Expr

-- Forward definition
@[extern "lean_grind_internalize"]
opaque internalize (e : Expr) (generation : Nat) (parent? : Option Expr := none) : GoalM Unit

-- Forward definition
@[extern "lean_grind_process_new_eqs"]
opaque processNewEqs : GoalM Unit

/--
Returns a proof that `a = b` if they have the same type. Otherwise, returns a proof of `HEq a b`.
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
Closes the current goal using the given proof of `False` and
marks it as inconsistent if it is not already marked so.
-/
def closeGoal (falseProof : Expr) : GoalM Unit := do
  markAsInconsistent
  let mvarId := (← get).mvarId
  unless (← mvarId.isAssigned) do
    let target ← mvarId.getType
    if target.isFalse then
      mvarId.assign falseProof
    else
      mvarId.assign (← mkFalseElim target falseProof)

def Goal.getENodes (goal : Goal) : Array ENode :=
  -- We must sort because we are using pointer addresses as keys in `enodes`
  let nodes := goal.enodes.toArray.map (·.2)
  nodes.qsort fun a b => a.idx < b.idx

/-- Returns all enodes in the goal -/
def getENodes : GoalM (Array ENode) := do
  return (← get).getENodes

/-- Executes `f` to each term in the equivalence class containing `e` -/
@[inline] def traverseEqc (e : Expr) (f : ENode → GoalM Unit) : GoalM Unit := do
  let mut curr := e
  repeat
    let n ← getENode curr
    f n
    if isSameExpr n.next e then return ()
    curr := n.next

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
  let nodes ← getENodes
  for n in nodes do
    f n

def filterENodes (p : ENode → GoalM Bool) : GoalM (Array ENode) := do
  let ref ← IO.mkRef #[]
  forEachENode fun n => do
    if (← p n) then
      ref.modify (·.push n)
  ref.get

def forEachEqcRoot (f : ENode → GoalM Unit) : GoalM Unit := do
  let nodes ← getENodes
  for n in nodes do
    if isSameExpr n.self n.root then
      f n

abbrev Propagator := Expr → GoalM Unit
abbrev Fallback := GoalM Unit

structure Methods where
  propagateUp   : Propagator := fun _ => return ()
  propagateDown : Propagator := fun _ => return ()
  fallback      : Fallback := pure ()
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

def applyFallback : GoalM Unit := do
  let fallback : GoalM Unit := (← getMethods).fallback
  fallback

/-- Returns expressions in the given expression equivalence class. -/
partial def Goal.getEqc (goal : Goal) (e : Expr) : List Expr :=
  go e e []
where
  go (first : Expr) (e : Expr) (acc : List Expr) : List Expr := Id.run do
    let some next ← goal.getNext? e | acc
    let acc := e :: acc
    if isSameExpr first next then
      return acc
    else
      go first next acc

@[inline, inherit_doc Goal.getEqc]
partial def getEqc (e : Expr) : GoalM (List Expr) :=
  return (← get).getEqc e

/-- Returns all equivalence classes in the current goal. -/
partial def Goal.getEqcs (goal : Goal) : List (List Expr) := Id.run do
  let mut r : List (List Expr) := []
  let nodes ← goal.getENodes
  for node in nodes do
    if isSameExpr node.root node.self then
      r := goal.getEqc node.self :: r
  return r

@[inline, inherit_doc Goal.getEqcs]
def getEqcs : GoalM (List (List Expr)) :=
  return (← get).getEqcs

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

/--
Returns extensionality theorems for the given type if available.
If `Config.ext` is `false`, the result is `#[]`.
-/
def getExtTheorems (type : Expr) : GoalM (Array Ext.ExtTheorem) := do
  unless (← getConfig).ext do return #[]
  if let some thms := (← get).extThms.find? { expr := type } then
    return thms
  else
    let thms ← Ext.getExtTheorems type
    modify fun s => { s with extThms := s.extThms.insert { expr := type } thms }
    return thms

/--
Helper function for instantiating a type class `type`, and
then using the result to perform `isDefEq x val`.
-/
def synthesizeInstanceAndAssign (x type : Expr) : MetaM Bool := do
  let .some val ← trySynthInstance type | return false
  isDefEq x val

end Lean.Meta.Grind
