/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.AlphaShareCommon
public import Lean.Meta.CongrTheorems
public section
namespace Lean.Meta.Sym

register_builtin_option sym.debug : Bool := {
  defValue := false
  descr    := "check invariants"
}

builtin_initialize registerTraceClass `sym.issues

/-!
## Sym Extensions

Extensible state mechanism for `SymM`, allowing modules to register persistent state
that lives across `simp` invocations within a `sym =>` block. Follows the same pattern
as `Grind.SolverExtension` in `Lean/Meta/Tactic/Grind/Types.lean`.
-/

/-- Opaque extension state type used to store type-erased extension values. -/
opaque SymExtensionStateSpec : (α : Type) × Inhabited α := ⟨Unit, ⟨()⟩⟩
@[expose] def SymExtensionState : Type := SymExtensionStateSpec.fst
instance : Inhabited SymExtensionState := SymExtensionStateSpec.snd

/--
A registered extension for `SymM`. Each extension gets a unique index into the
extensions array in `Sym.State`. Can only be created via `registerSymExtension`.
-/
structure SymExtension (σ : Type) where private mk ::
  id        : Nat
  mkInitial : IO σ
  deriving Inhabited

private builtin_initialize symExtensionsRef : IO.Ref (Array (SymExtension SymExtensionState)) ← IO.mkRef #[]

/--
Registers a new `SymM` state extension. Extensions can only be registered during initialization.
Returns a handle for typed access to the extension's state.
-/
def registerSymExtension {σ : Type} (mkInitial : IO σ) : IO (SymExtension σ) := do
  unless (← initializing) do
    throw (IO.userError "failed to register `Sym` extension, extensions can only be registered during initialization")
  let exts ← symExtensionsRef.get
  let id := exts.size
  let ext : SymExtension σ := { id, mkInitial }
  symExtensionsRef.modify fun exts => exts.push (unsafe unsafeCast ext)
  return ext

/-- Returns initial state for all registered extensions. -/
def SymExtensions.mkInitialStates : IO (Array SymExtensionState) := do
  let exts ← symExtensionsRef.get
  exts.mapM fun ext => ext.mkInitial

/--
Information about a single argument position in a function's type signature.

This is used during pattern matching and structural definitional equality tests
to identify arguments that can be skipped or handled specially
(e.g., instance arguments can be synthesized, proof arguments can be inferred).
-/
public structure ProofInstArgInfo where
  /-- `true` if this argument is a proof (its type is a `Prop`). -/
  isProof    : Bool
  /-- `true` if this argument is a type class instance. -/
  isInstance : Bool
  deriving Inhabited

/--
Information about a function symbol. It stores which argument positions are proofs or instances,
enabling optimizations during pattern matching and structural definitional equality tests
such as skipping proof arguments or deferring instance synthesis.
-/
public structure ProofInstInfo where
  /-- Information about each argument position. -/
  argsInfo : Array ProofInstArgInfo
  deriving Inhabited

/--
Information on how to build congruence proofs for function applications.
This enables efficient rewriting of subterms without repeatedly inferring types or instances.
-/
inductive CongrInfo where
  | /-- None of the arguments of the function can be rewritten. -/
    none
  | /--
    For functions with a fixed prefix of implicit/instance arguments followed by
    explicit non-dependent arguments that can be rewritten independently.

    - `prefixSize`: Number of leading arguments (types, instances) that are determined
      by the suffix arguments and should not be rewritten directly.
    - `suffixSize`: Number of trailing arguments that can be rewritten using simple congruence.

    Examples (showing `prefixSize`, `suffixSize`):
    - `HAdd.hAdd {α β γ} [HAdd α β γ] (a : α) (b : β)`: `(4, 2)` — rewrite `a` and `b`
    - `And (p q : Prop)`: `(0, 2)` — rewrite both propositions
    - `Eq {α} (a b : α)`: `(1, 2)` — rewrite `a` and `b`, type `α` is fixed
    - `Neg.neg {α} [Neg α] (a : α)`: `(2, 1)` — rewrite just `a`
    -/
    fixedPrefix (prefixSize : Nat) (suffixSize : Nat)
  | /--
    For functions with interlaced rewritable and non-rewritable arguments.
    Each element indicates whether the corresponding argument position can be rewritten.

    Example: For `HEq {α : Sort u} (a : α) {β : Sort u} (b : β)`, the mask would be
    `#[false, true, false, true]` — we can rewrite `a` and `b`, but not `α` or `β`.
    -/
    interlaced (rewritable : Array Bool)
  | /--
    For functions that have proofs and `Decidable` arguments. For this kind of function we generate
    a custom theorem.
    Example: `Array.eraseIdx {α : Type u} (xs : Array α) (i : Nat) (h : i < xs.size) : Array α`.
    The proof argument `h` depends on `xs` and `i`. To be able to rewrite `xs` and `i`, we use the
    auto-generated theorem.
    ```
    Array.eraseIdx.congr_simp {α : Type u} (xs xs' : Array α) (e_xs : xs = xs')
        (i i' : Nat) (e_i : i = i') (h : i < xs.size) : xs.eraseIdx i h = xs'.eraseIdx i' ⋯
    ```
    -/
    congrTheorem (thm : CongrTheorem)

/-- Pre-shared expressions for commonly used terms. -/
structure SharedExprs where
  trueExpr   : Expr
  falseExpr  : Expr
  natZExpr   : Expr
  btrueExpr  : Expr
  bfalseExpr : Expr
  ordEqExpr  : Expr
  intExpr    : Expr

/-- Configuration options for the symbolic computation framework. -/
structure Config where
  /-- When `true`, issues are collected during proof search and reported on failure. -/
  verbose : Bool := true
  deriving Inhabited

/-- Readonly context for the symbolic computation framework. -/
structure Context where
  sharedExprs : SharedExprs
  config      : Config := {}

structure Canon.State where
  /-- Cache for value-level canonicalization (no type reductions applied). -/
  cache       : Std.HashMap Expr Expr := {}
  /-- Cache for type-level canonicalization (reductions applied). -/
  cacheInType : Std.HashMap Expr Expr := {}

/-- Mutable state for the symbolic computation framework. -/
structure State where
  /-- `ShareCommon` (aka `Hash-consing`) state. -/
  share : AlphaShareCommon.State := {}
  /--
  Maps expressions to their maximal free variable (by declaration index).

  - `maxFVar[e] = some fvarId` means `fvarId` is the free variable with the largest declaration
    index occurring in `e`.
  - `maxFVar[e] = none` means `e` contains no free variables (but may contain metavariables).

  Recall that if `e` contains a metavariable `?m`, then we assume `e` may contain any free variable
  in the local context associated with `?m`.

  This mapping enables O(1) local context compatibility checks during metavariable assignment.
  Instead of traversing local contexts with `isSubPrefixOf`, we check if the maximal free variable
  in the assigned value is in scope of the metavariable's local context.

  **Note**: We considered using a mapping `PHashMap ExprPtr FVarId`. However, there is a corner
  case that is not supported by this representation. `e` contains a metavariable (with an empty local context),
  and no free variables.
  -/
  maxFVar : PHashMap ExprPtr (Option FVarId) := {}
  proofInstInfo : PHashMap Name (Option ProofInstInfo) := {}
  /--
  Cache for `inferType` results, keyed by pointer equality.
  `SymM` uses a fixed configuration, so we can use a simpler key than `MetaM`.
  Remark: type inference is a bottleneck on `Meta.Tactic.Simp` simplifier.
  -/
  inferType : PHashMap ExprPtr Expr := {}
  /--
  Cache for `getLevel` results, keyed by pointer equality.
  -/
  getLevel : PHashMap ExprPtr Level := {}
  congrInfo : PHashMap ExprPtr CongrInfo := {}
  /-- Cache for `isDefEqI` results -/
  defEqI : PHashMap (ExprPtr × ExprPtr) Bool := {}
  /-- State for registered `SymExtension`s, indexed by extension id. -/
  extensions : Array SymExtensionState := #[]
  /--
  Issues found during symbolic computation. Accumulated across operations
  within a `sym =>` block and reported when a tactic fails.
  -/
  issues : List MessageData := []
  canon : Canon.State := {}
  debug : Bool := false

abbrev SymM := ReaderT Context <| StateRefT State MetaM

private def mkSharedExprs : AlphaShareCommonM SharedExprs := do
  let falseExpr  ← shareCommonAlphaInc <| mkConst ``False
  let trueExpr   ← shareCommonAlphaInc  <| mkConst ``True
  let bfalseExpr ← shareCommonAlphaInc  <| mkConst ``Bool.false
  let btrueExpr  ← shareCommonAlphaInc  <| mkConst ``Bool.true
  let natZExpr   ← shareCommonAlphaInc  <| mkNatLit 0
  let ordEqExpr  ← shareCommonAlphaInc  <| mkConst ``Ordering.eq
  let intExpr    ← shareCommonAlphaInc  <| Int.mkType
  return { falseExpr, trueExpr, bfalseExpr, btrueExpr, natZExpr, ordEqExpr, intExpr }

def SymM.run (x : SymM α) : MetaM α := do
  let (sharedExprs, share) := mkSharedExprs |>.run {}
  let debug := sym.debug.get (← getOptions)
  let extensions ← SymExtensions.mkInitialStates
  x { sharedExprs } |>.run' { debug, share, extensions }

/-- Returns maximally shared commonly used terms -/
def getSharedExprs : SymM SharedExprs :=
  return (← read).sharedExprs

/-- Returns the internalized `True` constant.  -/
def getTrueExpr : SymM Expr := return (← getSharedExprs).trueExpr
/-- Returns `true` if `e` is the internalized `True` expression.  -/
def isTrueExpr (e : Expr) : SymM Bool := return isSameExpr e (← getTrueExpr)
/-- Returns the internalized `False` constant.  -/
def getFalseExpr : SymM Expr := return (← getSharedExprs).falseExpr
/-- Returns `true` if `e` is the internalized `False` expression.  -/
def isFalseExpr (e : Expr) : SymM Bool := return isSameExpr e (← getFalseExpr)
/-- Returns the internalized `Bool.true`.  -/
def getBoolTrueExpr : SymM Expr := return (← getSharedExprs).btrueExpr
/-- Returns `true` if `e` is the internalized `Bool.true` expression.  -/
def isBoolTrueExpr (e : Expr) : SymM Bool := return isSameExpr e (← getBoolTrueExpr)
/-- Returns the internalized `Bool.false`.  -/
def getBoolFalseExpr : SymM Expr := return (← getSharedExprs).bfalseExpr
/-- Returns `true` if `e` is the internalized `Bool.false` expression.  -/
def isBoolFalseExpr (e : Expr) : SymM Bool := return isSameExpr e (← getBoolFalseExpr)
/-- Returns the internalized `0 : Nat` numeral.  -/
def getNatZeroExpr : SymM Expr := return (← getSharedExprs).natZExpr
/-- Returns the internalized `Ordering.eq`.  -/
def getOrderingEqExpr : SymM Expr := return (← getSharedExprs).ordEqExpr
/-- Returns the internalized `Int`.  -/
def getIntExpr : SymM Expr := return (← getSharedExprs).intExpr

/--
Applies hash-consing to `e`. Recall that all expressions in a `grind` goal have
been hash-consed. We perform this step before we internalize expressions.
-/
def shareCommon (e : Expr) : SymM Expr := do
  let share ← modifyGet fun s => (s.share, { s with share := {} })
  let (e, share) := shareCommonAlpha e share
  modify fun s => { s with share }
  return e

/--
Incremental variant of `shareCommon` for expressions constructed from already-shared subterms.

Use this when an expression `e` was produced by a Lean API (e.g., `inferType`, `mkApp4`) that
does not preserve maximal sharing, but the inputs to that API were already maximally shared.

Unlike `shareCommon`, this function does not use a local `Std.HashMap ExprPtr Expr` to
track visited nodes. This is more efficient when the number of new (unshared) nodes is small,
which is the common case when wrapping API calls that build a few constructor nodes around
shared inputs.

Example:
```
-- `a` and `b` are already maximally shared
let result := mkApp2 f a b  -- result is not maximally shared
let result ← shareCommonInc result -- efficiently restore sharing
```
-/
def shareCommonInc (e : Expr) : SymM Expr := do
  let share ← modifyGet fun s => (s.share, { s with share := {} })
  let (e, share) := shareCommonAlphaInc e share
  modify fun s => { s with share }
  return e

@[inherit_doc shareCommonInc]
abbrev share (e : Expr) : SymM Expr :=
  shareCommonInc e

/-- Returns `true` if `sym.debug` is set -/
@[inline] def isDebugEnabled : SymM Bool :=
  return (← get).debug

def getConfig : SymM Config :=
  return (← readThe Context).config

/-- Adds an issue message to the issue tracker. -/
def reportIssue (msg : MessageData) : SymM Unit := do
  let msg ← addMessageContext msg
  modify fun s => { s with issues := .trace { cls := `issue } msg #[] :: s.issues }
  trace[sym.issues] msg

/-- Reports an issue if `verbose` mode is enabled. Does nothing if `verbose` is `false`. -/
@[inline] def reportIssueIfVerbose (msg : MessageData) : SymM Unit := do
  if (← getConfig).verbose then
    reportIssue msg

private meta def expandReportIssueMacro (s : Syntax) : MacroM (TSyntax `doElem) := do
  let msg ← if s.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| Sym.reportIssueIfVerbose $msg)

/-- Reports an issue if `verbose` mode is enabled. -/
macro "reportIssue!" s:(interpolatedStr(term) <|> term) : doElem => do
  expandReportIssueMacro s.raw

/-- Reports an issue if both `verbose` and `sym.debug` are enabled. Does nothing otherwise. -/
@[inline] def reportDbgIssue (msg : MessageData) : SymM Unit := do
  if (← getConfig).verbose then
    if sym.debug.get (← getOptions) then
      reportIssue msg

meta def expandReportDbgIssueMacro (s : Syntax) : MacroM (TSyntax `doElem) := do
  let msg ← if s.getKind == interpolatedStrKind then `(m! $(⟨s⟩)) else `(($(⟨s⟩) : MessageData))
  `(doElem| Sym.reportDbgIssue $msg)

/-- Similar to `reportIssue!`, but only reports issue if `sym.debug` is set to `true`. -/
macro "reportDbgIssue!" s:(interpolatedStr(term) <|> term) : doElem => do
  expandReportDbgIssueMacro s.raw

/-- Returns all accumulated issues without clearing them. -/
def getIssues : SymM (List MessageData) :=
  return (← get).issues

/--
Runs `x` with a fresh issue context. Issues reported during `x` are
prepended to the issues that existed before the call.
-/
def withNewIssueContext (x : SymM α) : SymM α := do
  let saved := (← get).issues
  modify fun s => { s with issues := [] }
  try x finally modify fun s => { s with issues := s.issues ++ saved }

/-- Similar to `Meta.isDefEqI`, but the result is cache using pointer equality. -/
def isDefEqI (s t : Expr) : SymM Bool := do
  let key := (⟨s⟩, ⟨t⟩)
  if let some result := (← get).defEqI.find? key then
    return result
  let result ← Meta.isDefEqI s t
  modify fun s => { s with defEqI := s.defEqI.insert key result }
  return result

instance : Inhabited (SymM α) where
  default := throwError "<SymM default value>"

/-! ### SymExtension accessors -/

private unsafe def SymExtension.getStateCoreImpl (ext : SymExtension σ) (extensions : Array SymExtensionState) : IO σ :=
  return unsafeCast extensions[ext.id]!

@[implemented_by SymExtension.getStateCoreImpl]
opaque SymExtension.getStateCore (ext : SymExtension σ) (extensions : Array SymExtensionState) : IO σ

def SymExtension.getState (ext : SymExtension σ) : SymM σ := do
  ext.getStateCore (← get).extensions

private unsafe def SymExtension.modifyStateImpl (ext : SymExtension σ) (f : σ → σ) : SymM Unit := do
  modify fun s => { s with
    extensions := s.extensions.modify ext.id fun state => unsafeCast (f (unsafeCast state))
  }

@[implemented_by SymExtension.modifyStateImpl]
opaque SymExtension.modifyState (ext : SymExtension σ) (f : σ → σ) : SymM Unit

end Lean.Meta.Sym
