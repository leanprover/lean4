/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Data.AssocList
import Lean.Util.FoldConsts
import Lean.Meta.SynthInstance
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.AbstractS
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Sym.IsClass
import Lean.Meta.Sym.MaxFVar
import Lean.Meta.Sym.ProofInstInfo
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.LitValues
import Lean.Meta.Sym.Offset
namespace Lean.Meta.Sym
open Internal

/-!
This module implements efficient pattern matching and unification module for the symbolic simulation
framework (`Sym`). The design prioritizes performance by using a two-phase approach:

# Phase 1 (Syntactic Matching)
- Patterns use de Bruijn indices for expression variables and renamed level params (`_uvar.0`, `_uvar.1`, ...) for universe variables
- Matching is purely structural after reducible definitions are unfolded during preprocessing
- Universe levels treat `max` and `imax` as uninterpreted functions (no AC reasoning)
- Binders and term metavariables are deferred to Phase 2

# Phase 2 (Pending Constraints)
- Handles binders (Miller patterns) and metavariable unification
- Converts remaining de Bruijn variables to metavariables
- Falls back to structural `isDefEqS` when necessary.
- It still uses the standard `isDefEq` for instances.

# Key design decisions:
- Preprocessing unfolds reducible definitions and performs beta/zeta reduction
- Kernel projections are expected to be folded as projection applications before matching
- Assignment conflicts are deferred to pending rather than invoking `isDefEq` inline
- `instantiateRevS` ensures maximal sharing of result expressions
-/

/-- Helper function for checking whether types `α` and `β` are definitionally equal during unification/matching. -/
def isDefEqTypes (α β : Expr) : MetaM Bool := do
  withReducible <| isDefEq α β

/--
Collects `ProofInstInfo` for all function symbols occurring in `pattern`.

Only includes functions that have at least one proof or instance argument.
-/
def mkProofInstInfoMapFor (pattern : Expr) : MetaM (AssocList Name ProofInstInfo) := do
  let cs := pattern.getUsedConstants
  let mut fnInfos := {}
  for declName in cs do
    if let some info ← mkProofInstInfo? declName then
      fnInfos := fnInfos.insertNew declName info
  return fnInfos

public structure Pattern where
  levelParams    : List Name
  varTypes       : Array Expr
  isInstance     : Array Bool
  pattern        : Expr
  fnInfos        : AssocList Name ProofInstInfo
  /--
  If `checkTypeMask? = some mask`, then we must check the type of pattern variable `i`
  if `mask[i]` is true.
  Moreover `mask.size == varTypes.size`.
  See `mkCheckTypeMask`
  -/
  checkTypeMask? : Option (Array Bool)
  deriving Inhabited

def uvarPrefix : Name := `_uvar

def isUVar? (n : Name) : Option Nat := Id.run do
  let .num p idx := n | return none
  unless p == uvarPrefix do return none
  return some idx

/-- Helper function for implementing `mkPatternFromDecl` and `mkEqPatternFromDecl` -/
def preprocessPattern (declName : Name) : MetaM (List Name × Expr) := do
  let info ← getConstInfo declName
  let levelParams := info.levelParams.mapIdx fun i _ => Name.num uvarPrefix i
  let us := levelParams.map mkLevelParam
  let type ← instantiateTypeLevelParams info.toConstantVal us
  let type ← preprocessType type
  return (levelParams, type)

/--
Creates a mask indicating which pattern variables require type checking during matching.

When matching a pattern against a target expression, we must ensure that pattern variable
assignments are type-correct. However, checking types for every variable is expensive.
This function identifies which variables actually need type checking.

**Key insight**: A pattern variable appearing as an argument to a function application
does not need its type checked separately, because the type information is already
encoded in the application structure, and we assume the input is type correct.

**Variables that need type checking**:
- Variables in function position: `f x` where `f` is a pattern variable
- Variables in binder domains or bodies: `∀ x : α, β` or `fun x : α => b`
- Variables appearing alone (not as part of any application)

**Variables that skip type checking**:
- Variables appearing only as arguments to applications: in `f x`, the variable `x`
  does not need checking because the type of `f` constrains the type of `x`

**Examples**:
- `bv0_eq (x : BitVec 0) : x = 0`: pattern is just `x`, must check type to ensure `BitVec 0`
- `forall_true : (∀ _ : α, True) = True`: `α` appears in binder domain, must check
- `Nat.add_zero (x : Nat) : x + 0 = x`: `x` is argument to `HAdd.hAdd`, no check needed

**Note**: This analysis is conservative. It may mark some variables for checking even when
the type information is redundant (already determined by other constraints). This is
harmless—just extra work, not incorrect behavior.

Returns an array of booleans parallel to the pattern's `varTypes`, where `true` indicates
the variable's type must be checked against the matched subterm's type.
-/
def mkCheckTypeMask (pattern : Expr) (numPatternVars : Nat) : Array Bool :=
  let mask := Array.replicate numPatternVars false
  go pattern 0 false mask
where
  go (e : Expr) (offset : Nat) (isArg : Bool) : Array Bool → Array Bool :=
    match e with
    | .app f a => go f offset isArg ∘ go a offset true
    | .letE .. => unreachable! -- We zeta-reduce at `preprocessType`
    | .const .. | .fvar _ | .sort _ | .mvar _ | .lit _ => id
    | .mdata _ b => go b offset isArg
    | .proj .. => id -- Should not occur in patterns
    | .forallE _ d b _
    | .lam _ d b _ => go d offset false ∘ go b (offset+1) false
    | .bvar idx => fun mask =>
      if idx >= offset && !isArg then
        let idx := idx - offset
        mask.set! (mask.size - idx - 1) true
      else
        mask

def mkPatternCore (levelParams : List Name) (varTypes : Array Expr) (isInstance : Array Bool)
    (pattern : Expr) : MetaM Pattern := do
  let fnInfos ← mkProofInstInfoMapFor pattern
  let checkTypeMask := mkCheckTypeMask pattern varTypes.size
  let checkTypeMask? := if checkTypeMask.all (· == false) then none else some checkTypeMask
  return { levelParams, varTypes, isInstance, pattern, fnInfos, checkTypeMask? }

/--
Creates a `Pattern` from the type of a theorem.

The pattern is constructed by stripping leading universal quantifiers from the theorem's type.
Each quantified variable becomes a pattern variable, with its type recorded in `varTypes` and
whether it is a type class instance recorded in `isInstance`. The remaining type after
stripping quantifiers becomes the `pattern` expression.

Universe level parameters are replaced with fresh unification variables (prefixed with `_uvar`).

If `num?` is `some n`, at most `n` leading quantifiers are stripped.
If `num?` is `none`, all leading quantifiers are stripped.
-/
public def mkPatternFromDecl (declName : Name) (num? : Option Nat := none) : MetaM Pattern := do
  let (levelParams, type) ← preprocessPattern declName
  let hugeNumber := 10000000
  let num := num?.getD hugeNumber
  let rec go (i : Nat) (type : Expr) (varTypes : Array Expr) (isInstance : Array Bool) : MetaM Pattern := do
    if i < num then
      if let .forallE _ d b _ := type then
        return (← go (i+1) b (varTypes.push d) (isInstance.push (isClass? (← getEnv) d).isSome))
    mkPatternCore levelParams varTypes isInstance type
  go 0 type #[] #[]

/--
Creates a `Pattern` from an equational theorem, using the left-hand side of the equation.
It also returns the right-hand side of the equation

Like `mkPatternFromDecl`, this strips all leading universal quantifiers, recording variable
types and instance status. However, instead of using the entire resulting type as the pattern,
it extracts just the LHS of the equation.

For a theorem `∀ x₁ ... xₙ, lhs = rhs`, returns a pattern matching `lhs` with `n` pattern variables.
Throws an error if the theorem's conclusion is not an equality.
-/
public def mkEqPatternFromDecl (declName : Name) : MetaM (Pattern × Expr) := do
  let (levelParams, type) ← preprocessPattern declName
  let rec go (type : Expr) (varTypes : Array Expr) (isInstance : Array Bool) : MetaM (Pattern × Expr) := do
    if let .forallE _ d b _ := type then
      return (← go b (varTypes.push d) (isInstance.push (isClass? (← getEnv) d).isSome))
    else
      let_expr Eq _ lhs rhs := type | throwError "resulting type for `{.ofConstName declName}` is not an equality"
      let pattern ← mkPatternCore levelParams varTypes isInstance lhs
      return (pattern, rhs)
  go type #[] #[]

structure UnifyM.Context where
  pattern   : Pattern
  unify     : Bool := true
  zetaDelta : Bool := true

structure UnifyM.State where
  eAssignment  : Array (Option Expr)   := #[]
  uAssignment  : Array (Option Level)  := #[]
  ePending     : Array (Expr × Expr)   := #[]
  uPending     : Array (Level × Level) := #[]
  iPending     : Array (Expr × Expr)   := #[]
  /--
  Contains the index of the pattern variables that we must check whether its type
  matches the type of the value assigned to it.
  -/
  tPending     : Array Nat             := #[]
  us           : List Level            := []
  args         : Array Expr            := #[]

abbrev UnifyM := ReaderT UnifyM.Context StateRefT UnifyM.State SymM

def pushPending (p : Expr) (e : Expr) : UnifyM Unit :=
  modify fun s => { s with ePending := s.ePending.push (p, e) }

def pushLevelPending (u : Level) (v : Level) : UnifyM Unit :=
  modify fun s => { s with uPending := s.uPending.push (u, v) }

def pushInstPending (p : Expr) (e : Expr) : UnifyM Unit :=
  modify fun s => { s with iPending := s.iPending.push (p, e) }

/--
Mark pattern variable `i` for type checking. That is, at the end of phase 1
we must check whether the type of this pattern variable is compatible with the type of
the value assigned to it.
-/
def pushCheckTypePending (i : Nat) : UnifyM Unit :=
  modify fun s => { s with tPending := s.tPending.push i }

def assignExprIfUnassigned (bidx : Nat) (e : Expr) : UnifyM Unit := do
  let s ← get
  let i := s.eAssignment.size - bidx - 1
  if s.eAssignment[i]!.isNone then
    modify fun s => { s with eAssignment := s.eAssignment.set! i (some e) }

def assignExpr (bidx : Nat) (e : Expr) : UnifyM Bool := do
  let s ← get
  let i := s.eAssignment.size - bidx - 1
  if let some e' := s.eAssignment[i]! then
    if isSameExpr e e' then return true
    else
      pushPending e' e
      return true
  else
    modify fun s => { s with eAssignment := s.eAssignment.set! i (some e) }
    if (← read).pattern.checkTypeMask?.isSome then
      pushCheckTypePending i
    return true

def assignLevel (uidx : Nat) (u : Level) : UnifyM Bool := do
  if let some u' := (← get).uAssignment[uidx]! then
    isLevelDefEq u u'
  else
    modify fun s => { s with uAssignment := s.uAssignment.set! uidx (some u) }
    return true

def processLevel (u : Level) (v : Level) : UnifyM Bool := do
  match u, v with
  | .zero, .zero => return true
  | .succ u, .succ v => processLevel u v
  | .zero, .succ _ => return false
  | .succ _, .zero => return false
  | .zero, .max v₁ v₂ => processLevel .zero v₁ <&&> processLevel .zero v₂
  | .max u₁ u₂, .zero => processLevel u₁ .zero <&&> processLevel u₂ .zero
  | .zero, .imax _ v => processLevel .zero v
  | .imax _ u, .zero => processLevel u .zero
  | .max u₁ u₂, .max v₁ v₂ => processLevel u₁ v₁ <&&> processLevel u₂ v₂
  | .imax u₁ u₂, .imax v₁ v₂ => processLevel u₁ v₁ <&&> processLevel u₂ v₂
  | .param uName, _ =>
    if let some uidx := isUVar? uName then
      assignLevel uidx v
    else if u == v then
      return true
    else if v.isMVar && (← read).unify then
      pushLevelPending u v
      return true
    else
      return false
  | .mvar _, _ | _, .mvar _ =>
    if (← read).unify then
      pushLevelPending u v
      return true
    else
      return false
  | _, _ => return false

def processLevels (us : List Level) (vs : List Level) : UnifyM Bool := do
  match us, vs with
  | [],    []    => return true
  | [],    _::_  => return false
  | _::_,  []    => return false
  | u::us, v::vs => processLevel u v <&&> processLevels us vs

/--
Returns `true` if `e` is an assigned metavariable.
-/
def isAssignedMVar (e : Expr) : MetaM Bool :=
  match e with
  | .mvar mvarId => mvarId.isAssigned
  | _            => return false

partial def process (p : Expr) (e : Expr) : UnifyM Bool := do
  match p with
  | .bvar bidx => assignExpr bidx e
  | .mdata _ p => process p e
  | .const declName us =>
    processConst declName us e <||> checkLetVar p e <||> checkMVar p e
  | .sort u =>
    processSort u e <||> checkLetVar p e <||> checkMVar p e
  | .app .. =>
    processApp p e <||> checkMVar p e
  | .forallE .. | .lam .. =>
    pushPending p e
    return true
  | .proj .. =>
    throwError "unexpected kernel projection term during unification/matching{indentExpr e}\npre-process and fold them as projection applications"
  | .fvar _ =>
    /-
    **Note**: Most patterns do not have free variables since they are created from
    top-level theorems. That said, some user may want to create patterns using local hypotheses, and they
    may contain free variables. This is not the common case. So, we just push to pending an continue.
    -/
    pushPending p e
    return true
  | .mvar _ | .lit _ =>
    pure (p == e) <||> checkLetVar p e <||> checkMVar p e
  | .letE .. => unreachable!
where
  checkMVar (p : Expr) (e : Expr) : UnifyM Bool := do
    if (← isAssignedMVar e) then
      process p (← instantiateMVarsS e)
    else if (← read).unify && e.getAppFn.isMVar then
      pushPending p e
      return true
    else
      return false

  checkLetVar (p : Expr) (e : Expr) : UnifyM Bool := do
    unless (← read).zetaDelta do return false
    let .fvar fvarId := e | return false
    let some value ← fvarId.getValue? | return false
    process p value

  processOffset (p : Offset) (e : Offset) : UnifyM Bool := do
   -- **Note** Recall that we don't assume patterns are maximally shared terms.
    match p, e with
    | .num _, .num _ => unreachable!
    | .num k₁, .add e k₂ =>
      if k₁ < k₂ then return false
      process (mkNatLit (k₁ - k₂)) e
    | .add p k₁, .num k₂ =>
      if k₂ < k₁ then return false
      process p (← share (mkNatLit (k₂ - k₁)))
    | .add p k₁, .add e k₂ =>
      if k₁ == k₂ then
        process p e
      else if k₁ < k₂ then
        if k₁ == 0 then return false
        process p (← share (mkNatAdd e (mkNatLit (k₂ - k₁))))
      else
        if k₂ == 0 then return false
        process (mkNatAdd p (mkNatLit (k₁ - k₂))) e

  processConstApp (declName : Name) (p : Expr) (e : Expr) : UnifyM Bool := do
    let some info := (← read).pattern.fnInfos.find? declName | process.processAppDefault p e
    let numArgs := p.getAppNumArgs
    processAppWithInfo p e (numArgs - 1) info

  processApp (p : Expr) (e : Expr) : UnifyM Bool := withIncRecDepth do
    let f := p.getAppFn
    let .const declName _ := f | processAppDefault p e
    if (← processConstApp declName p e) then
      return true
    else if let some p' := isOffset?' declName p then
      processOffset p' (toOffset e)
    else if let some e' := isOffset? e then
      processOffset (toOffset p) e'
    else
      return false

  processAppWithInfo (p : Expr) (e : Expr) (i : Nat) (info : ProofInstInfo) : UnifyM Bool := do
    let .app fp ap := p | if e.isApp then return false else process p e
    let .app fe ae := e | checkLetVar p e
    unless (← processAppWithInfo fp fe (i - 1) info) do return false
    if h : i < info.argsInfo.size then
      let argInfo := info.argsInfo[i]
      if argInfo.isInstance then
        if let .bvar bidx := ap then
          assignExprIfUnassigned bidx ae
        else
          pushInstPending ap ae
        return true
      else if argInfo.isProof then
        if let .bvar bidx := ap then
          assignExprIfUnassigned bidx ae
        return true
      else
        process ap ae
    else
      process ap ae

  processAppDefault (p : Expr) (e : Expr) : UnifyM Bool := do
    let .app fp ap := p | if e.isApp then return false else process p e
    let .app fe ae := e | checkLetVar p e
    unless (← processAppDefault fp fe) do return false
    process ap ae

  processConst (declName : Name) (us : List Level) (e : Expr) : UnifyM Bool := do
    let .const declName' us' := e | return false
    unless declName == declName' do return false
    processLevels us us'

  processSort (u : Level) (e : Expr) : UnifyM Bool := do
    let .sort v := e | return false
    processLevel u v

/--
Attempts to assign a level metavariable `u` to value `v`.
Returns `true` if `u` is an assignable level metavariable and the assignment succeeds.
Returns `false` if `u` is not a metavariable or is not assignable.
-/
def tryAssignLevelMVar (u : Level) (v : Level) : MetaM Bool := do
  let .mvar mvarId := u | return false
  unless (← isLevelMVarAssignable mvarId) do return false
  assignLevelMVar mvarId v
  return true

/--
Structural definitional equality for universe levels.
Treats `max` and `imax` as uninterpreted functions (no AC reasoning).
Attempts metavariable assignment in both directions if structural matching fails.
-/
def isLevelDefEqS (u : Level) (v : Level) : MetaM Bool := do
  match u, v with
  | .param u, .param v => return u == v
  | .zero, .zero => return true
  | .succ u, .succ v => isLevelDefEqS u v
  | .zero, .succ _ => return false
  | .succ _, .zero => return false
  | .zero, .max v₁ v₂ => isLevelDefEqS .zero v₁ <&&> isLevelDefEqS .zero v₂
  | .max u₁ u₂, .zero => isLevelDefEqS u₁ .zero <&&> isLevelDefEqS u₂ .zero
  | .zero, .imax _ v => isLevelDefEqS .zero v
  | .imax _ u, .zero => isLevelDefEqS u .zero
  | .max u₁ u₂, .max v₁ v₂ => isLevelDefEqS u₁ v₁ <&&> isLevelDefEqS u₂ v₂
  | .imax u₁ u₂, .imax v₁ v₂ => isLevelDefEqS u₁ v₁ <&&> isLevelDefEqS u₂ v₂
  | _, _ => tryAssignLevelMVar u v <||> tryAssignLevelMVar v u

/--
Structural definitional equality for lists of universe levels.
Returns `true` iff the lists have the same length and corresponding elements are structurally equal.
-/
def isLevelDefEqListS (us : List Level) (vs : List Level) : MetaM Bool := do
  match us, vs with
  | [],    []    => return true
  | [],    _::_  => return false
  | _::_,  []    => return false
  | u::us, v::vs => isLevelDefEqS u v <&&> isLevelDefEqListS us vs

/--
Context for structural definitional equality (`isDefEqS`).
-/
structure DefEqM.Context where
  unify : Bool := true
  /--
  If `zetaDelta` is `true`, then zeta-delta reduction is allowed.
  That is, `isDefEqS` can unfold `x` if the local context contains `(x : t := v)`.
  -/
  zetaDelta : Bool := true
  /--
  The next declaration index at the entry point of `isDefEqS`.
  This information is used to decide whether an application is a Miller pattern or not.
  -/
  lctxInitialNextIndex : Nat := 0
  /--
  If `unify` is `false`, it contains which variables can be assigned.
  -/
  mvarsNew : Array MVarId := #[]
  /--
  If a metavariable is in this collection, when we perform the assignment `?m := v`,
  we must check whether their types are compatible.
  -/
  mvarsToCheckType : Array MVarId := #[]

abbrev DefEqM := ReaderT DefEqM.Context SymM

/--
Structural definitional equality. It is much cheaper than `isDefEq`.

This function is the main loop of `isDefEqS`
-/
@[extern "lean_sym_def_eq"] -- Forward definition
opaque isDefEqMain : Expr → Expr → DefEqM Bool

/--
Structural definitional equality for `forall` and `lambda` binders.
Opens all binders simultaneously, then checks domain equality and body equality.
This approach avoids repeated `withLCtx` calls for each binder.
-/
def isDefEqBindingS (a b : Expr) : DefEqM Bool := do
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  go lctx localInsts #[] a b #[]
where
  checkDomains (fvars : Array Expr) (ds₂ : Array Expr) : DefEqM Bool := do
    for fvar in fvars, d in ds₂ do
      let fvarType ← fvar.fvarId!.getType
      unless (← isDefEqMain fvarType d) do return false
    return true

  go (lctx : LocalContext) (localInsts : LocalInstances) (fvars : Array Expr) (e₁ e₂ : Expr) (ds₂ : Array Expr) : DefEqM Bool := do
    match e₁, e₂ with
    | .forallE n d₁ b₁ _, .forallE _ d₂ b₂ _
    | .lam     n d₁ b₁ _, .lam     _ d₂ b₂ _ =>
      let d₁     ← instantiateRevS d₁ fvars
      let d₂     ← instantiateRevS d₂ fvars
      let fvarId ← mkFreshFVarId
      let fvar   ← mkFVarS fvarId
      let lctx   := lctx.mkLocalDecl fvarId n d₁
      let localInsts := if let some className := isClass? (← getEnv) d₁ then
        localInsts.push { className, fvar }
      else
        localInsts
      go lctx localInsts (fvars.push fvar) b₁ b₂ (ds₂.push d₂)
    | _, _ => withLCtx lctx localInsts do
      unless (← checkDomains fvars ds₂) do return false
      isDefEqMain (← instantiateRevS e₁ fvars) (← instantiateRevS e₂ fvars)

/--
Returns `true` if the metavariable `mvarId` can be assigned in the current context.
When `unify` is `true`, uses the default condition (not read-only nor synthetic opaque).
When `unify` is `false`, only metavariables in `mvarsNew` can be assigned. That is,
only metavariables associated with pattern variables can be assigned.
-/
def isAssignableMVar (mvarId : MVarId) : DefEqM Bool := do
  if (← read).unify then
    -- Use default condition
    return !(← mvarId.isReadOnlyOrSyntheticOpaque)
  else
    return (← read).mvarsNew.contains mvarId

/--
Checks whether `e` satisfies the Miller pattern condition on its arguments.

Returns `true` if `e` is not an application, or `e` is an n-ary application `f a₁ ... aₙ`
where all arguments are pairwise distinct free variables that were introduced during the
current `isDefEqS` invocation (i.e., their declaration index is ≥ `lctxInitialNextIndex`).

This condition is essential for higher-order unification: when assigning a metavariable
`?m a₁ ... aₙ := rhs`, the Miller pattern restriction ensures there is a unique solution
`?m := fun x₁ ... xₙ => rhs[aᵢ/xᵢ]`. The index check ensures we only consider variables
bound by the binders being compared, not pre-existing free variables from the context.

Examples:
- `f x y z` where `x`, `y`, `z` are distinct, newly-introduced free variables → `true`
- `f x c z` where `c` is a constant → `false` (non-variable argument)
- `f x y x` → `false` (repeated variable)
- `f x y z` where `x` existed before `isDefEqS` was called → `false` (pre-existing variable)
- `f` (nullary) → `true`
-/
def isMillerPatternArgs (e : Expr) : DefEqM Bool := do
  let rec isUniqueArgUpTo (curr : Expr) (e' : Expr) (fvarId : FVarId) : Bool :=
    if isSameExpr curr e' then
      true
    else match curr with
      | .app f (.fvar fvarId') => fvarId != fvarId' && isUniqueArgUpTo f e' fvarId
      | _ => false
  let initialNextIndex := (← read).lctxInitialNextIndex
  let lctx ← getLCtx
  let rec go (e' : Expr) : Bool :=
    match e' with
    | .app f (.fvar fvarId) =>
      if let some localDecl := lctx.find? fvarId then
        localDecl.index ≥ initialNextIndex &&
        isUniqueArgUpTo e e' fvarId &&
        go f
      else
        false
    | .app _ _ => false
    | _ => true
  return go e

/--
Returns `true` if the maximal free variable in `s` is less than or equal to the maximal free variable
in `t`. We use this function when `t` is a metavariable, and we are trying to assign `t := s`.
-/
def mayAssign (t s : Expr) : SymM Bool := do
  let some sMaxFVarId ← getMaxFVar? s
    | return true -- `s` does not contain free variables
  let some tMaxFVarId ← getMaxFVar? t
    | return false
  let sMaxFVarDecl ← sMaxFVarId.getDecl
  let tMaxFVarDecl ← tMaxFVarId.getDecl
  return tMaxFVarDecl.index ≥ sMaxFVarDecl.index

@[inline] def whenUndefDo (x : DefEqM LBool) (k : DefEqM Bool) : DefEqM Bool := do
  match (← x) with
  | .true  => return true
  | .false => return false
  | .undef => k

/--
Attempts to solve a unification constraint `t =?= s` where `t` has the form `?m a₁ ... aₙ`
and satisfies the Miller pattern condition (all `aᵢ` are distinct, newly-introduced free variables).

If successful, assigns `?m := fun x₁ ... xₙ => s` and returns `true`.
Returns `false` if:
- `tFn` is not a metavariable
- `t` does not satisfy the Miller pattern condition
- The assignment would violate scope (free variables in `fun x₁ ... xₙ => s` not in scope of `?m`)

The `tFn` parameter must equal `t.getAppFn` (enforced by the proof argument).

Remark: `t` may be of the form `?m`.
-/
def tryAssignMillerPattern (tFn : Expr) (t : Expr) (s : Expr) (_ : tFn = t.getAppFn) : DefEqM LBool := do
  let .mvar mvarId := tFn | return .undef
  if !(← isAssignableMVar mvarId) then return .undef
  if !(← isMillerPatternArgs t) then return .undef
  let s ← if t.isApp then
    mkLambdaFVarsS t.getAppArgs s
  else
    pure s
  if !(← mayAssign tFn s) then return .undef
  if (← read).mvarsToCheckType.contains mvarId then
    unless (← Sym.isDefEqTypes (← mvarId.getDecl).type (← inferType s)) do
      return .false
  mvarId.assign s
  return .true

/--
Structural definitional equality for applications without `ProofInstInfo`.
Recursively checks function and argument equality.
-/
def isDefEqAppDefault (t : Expr) (s : Expr) : DefEqM Bool := do
  let .app f₁ a₁ := t | if s.isApp then return false else isDefEqMain t s
  let .app f₂ a₂ := s | return false
  unless (← isDefEqAppDefault f₁ f₂) do return false
  isDefEqMain a₁ a₂

/--
Attempts to assign an unassigned metavariable on either side.
Tries `t := s` first, then `s := t`. Returns `true` if either assignment succeeds.
Used as a fast path before more expensive unification strategies. Example: using
more expensive `isDefEqI` for instance arguments.
-/
def tryAssignUnassigned (t : Expr) (s : Expr) : DefEqM Bool := do
  go t s <||> go s t
where
  go (t : Expr) (s : Expr) : DefEqM Bool := do
    let .mvar mvarId := t | return false
    if (← mvarId.isAssigned) then return false
    if !(← isAssignableMVar mvarId) then return false
    if !(← mayAssign t s) then return false
    /-
    **Note**: we don't need to check the type of `mvarId` here even if the variable is marked for
    checking. This is the case because `tryAssignUnassigned` is invoked only from a context where `t` and `s` are the arguments
    of function applications.
    -/
    mvarId.assign s
    return true

/--
Structural definitional equality for applications with `ProofInstInfo`.
Skips proof arguments (proof irrelevance) and defers instance arguments to `isDefEqI`.
-/
def isDefEqAppWithInfo (t : Expr) (s : Expr) (i : Nat) (info : ProofInstInfo) : DefEqM Bool := do
  let .app f₁ a₁ := t | if s.isApp then return false else isDefEqMain t s
  let .app f₂ a₂ := s | return false
  unless (← isDefEqAppWithInfo f₁ f₂ (i - 1) info) do return false
  if h : i < info.argsInfo.size then
    let argInfo := info.argsInfo[i]
    if argInfo.isInstance then
      if (← tryAssignUnassigned a₁ a₂) then
        return true
      else
        isDefEqI a₁ a₂
    else if argInfo.isProof then
      discard <| tryAssignUnassigned a₁ a₂
      return true
    else
      isDefEqMain a₁ a₂
  else
    isDefEqMain a₁ a₂

/--
Structural definitional equality for applications.
Looks up `ProofInstInfo` for the head constant and delegates to `isDefEqAppWithInfo`
if available, otherwise uses `isDefEqAppDefault`.
-/
def isDefEqApp (tFn : Expr) (t : Expr) (s : Expr) (_ : tFn = t.getAppFn) : DefEqM Bool := do
  unless t.isApp && s.isApp do return false
  let .const declName _ := tFn | isDefEqAppDefault t s
  let some info ← getProofInstInfo? declName | isDefEqAppDefault t s
  let numArgs := t.getAppNumArgs
  isDefEqAppWithInfo t s (numArgs - 1) info

/--
`isDefEqMain` implementation.
-/
@[export lean_sym_def_eq]
def isDefEqMainImpl (t : Expr) (s : Expr) : DefEqM Bool := do
  if isSameExpr t s then return true
  match t, s with
  | .lit  l₁,      .lit l₂       => return l₁ == l₂
  | .sort u,       .sort v       => isLevelDefEqS u v
  | .lam ..,       .lam ..       => isDefEqBindingS t s
  | .forallE ..,   .forallE ..   => isDefEqBindingS t s
  | .mdata _ t,    _             => isDefEqMain t s
  | _,             .mdata _ s    => isDefEqMain t s
  | .fvar fvarId₁, .fvar fvarId₂ =>
    if (← read).zetaDelta then
      if fvarId₁ == fvarId₂ then return true
      let decl₁ ← fvarId₁.getDecl
      let decl₂ ← fvarId₂.getDecl
      if !decl₁.isLet && !decl₂.isLet then
        -- Both are not let-declarations
        return false
      else if decl₁.index < decl₂.index then
        -- If `s` occurs after `t` and it is a let-decl, unfold and recurse
        let some val₂ := decl₂.value? | return false
        isDefEqMain t val₂
      else
        -- If `t` occurs after `s`, and it is a let-decl, unfold and recurse
        let some val₁ := decl₁.value? | return false
        isDefEqMain val₁ s
    else
      return fvarId₁ == fvarId₂
  | .const declName₁ us₁, .const declName₂ us₂ =>
    if declName₁ == declName₂ then
      isLevelDefEqListS us₁ us₂
    else
      return false
  | .bvar _, _ | _, .bvar _ => unreachable!
  | .proj .., _ | _, .proj .. =>
    throwError "unexpected kernel projection term during structural definitional equality{indentExpr t}\nand{indentExpr s}\npre-process and fold them as projection applications"
    return false
  | .letE .., _ | _, .letE .. =>
    throwError "unexpected let-declaration term during structural definitional equality{indentExpr t}\nand{indentExpr s}\npre-process and zeta-reduce them"
    return false
  | _, _ =>
    let tFn := t.getAppFn
    let sFn := s.getAppFn
    if (← isAssignedMVar tFn) then
      isDefEqMain (← instantiateMVarsS t) s
    else if (← isAssignedMVar sFn) then
      isDefEqMain t (← instantiateMVarsS s)
    else
    whenUndefDo (tryAssignMillerPattern tFn t s rfl) do
    whenUndefDo (tryAssignMillerPattern sFn s t rfl) do
    if let .fvar fvarId₁ := t then
      unless (← read).zetaDelta do return false
      let some val₁ ← fvarId₁.getValue? | return false
      isDefEqMain val₁ s
    else if let .fvar fvarId₂ := s then
      unless (← read).zetaDelta do return false
      let some val₂ ← fvarId₂.getValue? | return false
      isDefEqMain t val₂
    else
      isDefEqApp tFn t s rfl

abbrev DefEqM.run (unify := true) (zetaDelta := true) (mvarsNew : Array MVarId := #[])
    (mvarsToCheckType : Array MVarId := #[]) (x : DefEqM α) : SymM α := do
  let lctx ← getLCtx
  let lctxInitialNextIndex := lctx.decls.size
  x { zetaDelta, lctxInitialNextIndex, unify, mvarsNew, mvarsToCheckType }

/--
A lightweight structural definitional equality for the symbolic simulation framework.
Unlike the full `isDefEq`, it avoids expensive operations while still supporting Miller pattern unification.
-/
public def isDefEqS (t : Expr) (s : Expr) (unify := true) (zetaDelta := true)
    (mvarsNew : Array MVarId := #[]) (mvarsToCheckType : Array MVarId := #[]): SymM Bool := do
  DefEqM.run (unify := unify) (zetaDelta := zetaDelta) (mvarsNew := mvarsNew) (mvarsToCheckType := mvarsToCheckType) do
    isDefEqMain t s

def noPending : UnifyM Bool := do
  let s ← get
  return s.ePending.isEmpty && s.uPending.isEmpty && s.iPending.isEmpty

def instantiateLevelParamsS (e : Expr) (paramNames : List Name) (us : List Level) : SymM Expr :=
  -- We do not assume `e` is maximally shared
  shareCommon (e.instantiateLevelParams paramNames us)

inductive MkPreResultResult where
  | failed
  | success (mvarsToCheckType : Array MVarId)

def mkPreResult : UnifyM MkPreResultResult := do
  let us ← (← get).uAssignment.toList.mapM fun
    | some val => pure val
    | none => mkFreshLevelMVar
  let pattern := (← read).pattern
  let varTypes := pattern.varTypes
  let isInstance := pattern.isInstance
  let eAssignment := (← get).eAssignment
  let tPending := (← get).tPending
  let mut args := #[]
  let mut mvarsToCheckType := #[]
  for h : i in *...eAssignment.size do
    if let .some val := eAssignment[i] then
      if tPending.contains i then
        let type := varTypes[i]!
        let type ← instantiateLevelParamsS type pattern.levelParams us
        let type ← instantiateRevBetaS type args
        let valType ← inferType val
        -- **Note**: we have to use the default `isDefEq` because the type of `val`
        -- is not necessarily normalized.
        unless (← isDefEqTypes type valType) do
          return .failed
      args := args.push val
    else
      let type := varTypes[i]!
      let type ← instantiateLevelParamsS type pattern.levelParams us
      let type ← instantiateRevBetaS type args
      if isInstance[i]! then
        if let .some val ← trySynthInstance type then
          args := args.push (← shareCommon val)
          continue
      let mvar ← mkFreshExprMVar type
      let mvar ← shareCommon mvar
      if let some mask := (← read).pattern.checkTypeMask? then
        if mask[i]! then
          mvarsToCheckType := mvarsToCheckType.push mvar.mvarId!
      args := args.push mvar
  modify fun s => { s with args, us }
  return .success mvarsToCheckType

def processPendingLevel : UnifyM Bool := do
  let uPending := (← get).uPending
  if uPending.isEmpty then return true
  let pattern := (← read).pattern
  let us := (← get).us
  for (u, v) in uPending do
    let u := u.instantiateParams pattern.levelParams us
    unless (← isLevelDefEqS u v) do
      return false
  return true

def processPendingInst : UnifyM Bool := do
  let iPending := (← get).iPending
  if iPending.isEmpty then return true
  let pattern := (← read).pattern
  let us := (← get).us
  let args := (← get).args
  for (t, s) in iPending do
    let t ← instantiateLevelParamsS t pattern.levelParams us
    let t ← instantiateRevBetaS t args
    unless (← isDefEqI t s) do
      return false
  return true

def processPendingExpr (mvarsToCheckType : Array MVarId) : UnifyM Bool := do
  let ePending := (← get).ePending
  if ePending.isEmpty then return true
  let pattern := (← read).pattern
  let us := (← get).us
  let args := (← get).args
  let unify := (← read).unify
  let zetaDelta := (← read).zetaDelta
  let mvarsNew := if unify then #[] else args.filterMap fun
    | .mvar mvarId => some mvarId
    | _ => none
  DefEqM.run unify zetaDelta mvarsNew mvarsToCheckType do
    for (t, s) in ePending do
      let t ← instantiateLevelParamsS t pattern.levelParams us
      let t ← instantiateRevBetaS t args
      unless (← isDefEqMain t s) do
        return false
    return true

def processPending (mvarsToCheckType : Array MVarId) : UnifyM Bool := do
  if (← noPending) then
    return true
  else
    processPendingLevel <&&> processPendingInst <&&> processPendingExpr mvarsToCheckType

abbrev UnifyM.run (pattern : Pattern) (unify : Bool) (zetaDelta : Bool) (k : UnifyM α) : SymM α := do
  let eAssignment := pattern.varTypes.map fun _ => none
  let uAssignment := pattern.levelParams.toArray.map fun _ => none
  k { unify, zetaDelta, pattern } |>.run' { eAssignment, uAssignment }

public structure MatchUnifyResult where
  us : List Level
  args : Array Expr

def mkResult : UnifyM MatchUnifyResult := do
  let s ← get
  return { s with }

def main (p : Pattern) (e : Expr) (unify : Bool) (zetaDelta : Bool) : SymM (Option (MatchUnifyResult)) :=
  UnifyM.run p unify zetaDelta do
    unless (← process p.pattern e) do return none
    match (← mkPreResult) with
    | .failed => return none
    | .success mvarsToCheckType =>
      unless (← processPending mvarsToCheckType) do return none
      return some (← mkResult)

/--
Attempts to match expression `e` against pattern `p` using purely syntactic matching.

Returns `some result` if matching succeeds, where `result` contains:
- `us`: Level assignments for the pattern's universe variables
- `args`: Expression assignments for the pattern's bound variables

Matching fails if:
- The term contains metavariables (use `unify?` instead)
- Structural mismatch after reducible unfolding

Instance arguments are deferred for later synthesis. Proof arguments are
skipped via proof irrelevance.
-/
public def Pattern.match? (p : Pattern) (e : Expr) (zetaDelta := true) : SymM (Option (MatchUnifyResult)) :=
  main p e (unify := false) (zetaDelta := zetaDelta)

/--
Attempts to unify expression `e` against pattern `p`, allowing metavariables in `e`.

Returns `some result` if unification succeeds, where `result` contains:
- `us`: Level assignments for the pattern's universe variables
- `args`: Expression assignments for the pattern's bound variables

Unlike `match?`, this handles terms containing metavariables by deferring
constraints to Phase 2 unification. Use this when matching against goal
expressions that may contain unsolved metavariables.

Instance arguments are deferred for later synthesis. Proof arguments are
skipped via proof irrelevance.
-/
public def Pattern.unify? (p : Pattern) (e : Expr) (zetaDelta := true) : SymM (Option (MatchUnifyResult)) :=
  main p e (unify := true) (zetaDelta := zetaDelta)

end Lean.Meta.Sym
