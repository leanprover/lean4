/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Init.Data.Int.OfNat
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.ProofUtil
import Lean.Meta.Tactic.Simp.Arith.Int.Simp
import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
import Lean.Meta.Tactic.Grind.Arith.Cutsat.VarRename
import Lean.Meta.Sym.Arith.VarRename
import Lean.Meta.Sym.Arith.ToExpr
import Init.Data.Nat.Order
import Init.Data.Order.Lemmas
public section
namespace Lean.Meta.Grind.Arith.Cutsat
deriving instance Hashable for Int.Internal.Linear.Expr

/-!
State for the cutsat proof construction monad.

The final proof may reference only a small subset of the cutsat variables.
Thus, we normalize the variables and remove any that are unused from the context.
The variable order must be preserved, as the cutsat auxiliary theorems assume the polynomials are ordered.

Another complication is that cutsat may reorder variables during the search, possibly
several times. Each reordering starts a new epoch (see `State.varsHistory`), and a `.reorder c`
justification is the delimiter into the previous epoch: `c` and its dependencies use the
variable order of the epoch before the reordering. Every epoch has its own declarations and
variable contexts.

While constructing a proof, we use auxiliary free variables for variables, polynomials, expressions,
and the variable contexts. Cutsat also uses the ring solver to normalize nonlinear polynomials.
After construction, variables are renamed, and variables, polynomials, and expressions are replaced
with their (ground) values.

Constraints stored in the goal of an enclosing case split are hoisted: they are proved once in that
goal, and shared by all branches of the case split (see `hoisting`). A proof built in the goal of
the case split at depth `d` uses the variable contexts of depth `d`, which only contain the variables
of that goal. All proofs share one renaming: the cutsat and `CommRing` variables are numbered in
creation order, so the variables of an enclosing goal are renamed to a prefix of the renamed variables.
A cutsat variable context is declared in the outermost enclosing case split where its variables exist,
and a `CommRing` variable context in the case split at its depth. A variable context is shared by all
proofs that use an equal context (see `Grind.hoistDecl`).
-/
/-- Declarations of one variable-order epoch. -/
private structure EpochDecls where
  /-- Map from used variables to (temporary) free variable. -/
  varDecls  : Std.HashMap Var Expr := {}
  /-- Map from used polynomials to free variable. -/
  polyDecls : Std.HashMap Poly Expr := {}
  /-- Map from used cutsat expressions to free variable. -/
  exprDecls : Std.HashMap Int.Internal.Linear.Expr Expr := {}
  deriving Inhabited

/-- Auxiliary free variable for a variable context, see `getContext`. -/
private structure CtxVar where
  fvar : Expr

/-- Identifies a variable context of a `ProofM` run, see `getContext`. -/
private structure CtxKey where
  /-- Split depth of the goal where the context is used. -/
  depth : Nat
  /-- Epoch of the variables of the context. -/
  epoch : Nat
  deriving BEq, Hashable

/-- A proof in the cache of visited cutsat proof terms, see `caching`. -/
private structure CachedProof where
  /-- Split depth of the goal where the proof was built. The proof is valid in this goal and below it. -/
  depth : Nat
  /-- The proof, which uses auxiliary free variables, or the free variable of a hoisted fact. -/
  proof : Expr

/-- A fact hoisted to an enclosing case split, see `hoisting`. -/
private structure HoistedFact where
  /-- Split depth of the goal where the fact is proved. -/
  depth : Nat
  /-- Index of its declaration in `Grind.HoistedDecls.decls`, see `Grind.reserveHoistedDecl`. -/
  idx   : Nat
  /-- Its proof, which uses auxiliary free variables. -/
  proof : Expr

private structure ProofM.State where
  /-- Cache for visited cutsat proof terms. The key is the pointer address. -/
  cache         : Std.HashMap UInt64 CachedProof := {}
  /-- Declarations of each epoch, indexed by epoch. The last entry is the current order. -/
  decls         : Array EpochDecls := #[]
  /-- Map from used ring polynomials to free variable. -/
  ringPolyDecls : Std.HashMap CommRing.Poly Expr := {}
  /-- Map from used ring expressions to free variable. -/
  ringExprDecls : Std.HashMap CommRing.RingExpr Expr := {}
  /-- Variable contexts. -/
  ctxs          : Std.HashMap CtxKey CtxVar := {}
  /-- `CommRing` variable contexts, indexed by split depth. The `CommRing` variables have no epochs. -/
  ringCtxs      : Std.HashMap Nat CtxVar := {}
  /-- Facts hoisted to enclosing case splits. -/
  facts         : Array HoistedFact := #[]

private structure ProofM.Context where
  /-- Epoch of the justification being processed. Each `.reorder c` steps into the previous one. -/
  epoch     : Nat
  /-- Split depth of the goal whose state is used, see `withGoalAtDepth`. -/
  depth     : Nat
  /--
  `true` if a proof that abstracts a decision variable of the cutsat search is being constructed,
  e.g., `.ofDiseqSplit`. See `hoisting`.
  -/
  underDecVar : Bool := false

/-- Auxiliary monad for constructing cutsat proofs. -/
private abbrev ProofM := ReaderT ProofM.Context (StateRefT ProofM.State GoalM)

/--
Executes `k` in the previous epoch. We use this combinator to process `.reorder c`
justifications: `c` uses the variable order of the epoch before the reordering.
-/
private def withPrevEpoch (k : ProofM α) : ProofM α := do
  withReader (fun c => { c with epoch := c.epoch - 1 }) k

/-- Returns the variables of epoch `epoch` in the cutsat state `s`, if `s` has this epoch. -/
private def State.getEpochVars? (s : State) (epoch : Nat) : Option (PArray Expr) :=
  if epoch == s.varsHistory.size then
    some s.vars
  else if h : epoch < s.varsHistory.size then
    some s.varsHistory[epoch].1
  else
    none

/-- Returns the variables of epoch `epoch` in the goal `goal`. -/
private def getEpochVarsOf (goal : Goal) (epoch : Nat) : GoalM (PArray Expr) := do
  let some vars := (← cutsatExt.getStateCore goal).getEpochVars? epoch
    | throwError "`grind` internal error, cutsat epoch {epoch} is not available"
  return vars

/-- Returns the variables of epoch `epoch` in the current goal. -/
private def getEpochVars (epoch : Nat) : GoalM (PArray Expr) := do
  getEpochVarsOf (← get) epoch

/-- Returns the variables of the current epoch. -/
private def getCurrVars : ProofM (PArray Expr) := do
  getEpochVars (← read).epoch

/--
Returns the auxiliary free variable for the variable context of the current split depth and epoch,
see `mkProof`.
-/
private def getContext : ProofM Expr := do
  let key : CtxKey := { depth := (← read).depth, epoch := (← read).epoch }
  if let some ctx := (← get).ctxs[key]? then
    return ctx.fvar
  let fvar := mkFVar (← mkFreshFVarId)
  modify fun s => { s with ctxs := s.ctxs.insert key { fvar } }
  return fvar

/--
Returns the auxiliary free variable for the `CommRing` variable context of the current split depth,
needed for normalizing nonlinear polynomials, see `mkProof`.
-/
private def getRingContext : ProofM Expr := do
  let depth := (← read).depth
  if let some ctx := (← get).ringCtxs[depth]? then
    return ctx.fvar
  let fvar := mkFVar (← mkFreshFVarId)
  modify fun s => { s with ringCtxs := s.ringCtxs.insert depth { fvar } }
  return fvar

/--
Returns the mapping from expressions to cutsat variables of the current epoch.
These are variables before the renaming them.
-/
private def getVarMap : ProofM (PHashMap ExprPtr Var) := do
  let epoch := (← read).epoch
  let s ← get'
  if epoch == s.varsHistory.size then return s.varMap else return s.varsHistory[epoch]!.2

private def getVarOf (e : Expr) : ProofM Var := do
  let some x := (← getVarMap).find? { expr := e } | throwError "`grind` internal error, missing cutsat variable{indentExpr e}"
  return x

private def caching (c : α) (k : ProofM Expr) : ProofM Expr := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  let depth := (← read).depth
  if let some cached := (← get).cache[addr]? then
    if cached.depth ≤ depth then
      return cached.proof
  let proof ← k
  modify fun s => { s with cache := s.cache.insert addr { depth, proof } }
  return proof

/--
Executes `k` using the state of the goal of the enclosing case split at `depth`. The goal stack is not
changed, so declarations can still be hoisted to all enclosing case splits of the goal being proved.
The local context is not changed either, as it extends the one of the goal at `depth`.
-/
private def withGoalAtDepth (depth : Nat) (k : ProofM α) : ProofM α := do
  if depth == (← read).depth then
    return ← k
  let goal ← getThe Goal
  let some (_, s) := goal.goalStack[depth]?
    | throwError "`grind` internal error, no case split at depth {depth}"
  modifyThe Goal ({ · with toGoalState := { s with goalStack := goal.goalStack } })
  try withReader ({ · with depth }) k finally modifyThe Goal fun _ => goal

/--
If `c` was stored in the goal of an enclosing case split at depth `depth?`, returns a free variable
for its proof in that goal, which is shared by all subgoals of the case split
(see `Grind.reserveHoistedDecl`). Otherwise, returns `k`. The proof is `k` executed in the goal of the
case split, and it is declared after the facts it uses. The fact states `type e`, where `e` is the
denotation of `p` using the variables of the current epoch. If the proof is a free variable (e.g., a
hypothesis), it is returned without a declaration.

Nothing is hoisted while a proof that abstracts a decision variable of the cutsat search is being
constructed (see `underDecVar`), as the proof of `c` may contain the decision variable.

Remark: `depth?` may exceed the split depth of the goal whose state is used. The goal stack of a stuck
subgoal is truncated when its case split completes (see `Action.splitCore`), but the constraints stored
in it keep their depth. As the goal can only use constraints stored in it or in the goals of enclosing
case splits, we use its depth instead. Otherwise, the proof of `c` would be declared in a case split
below the one of the proof being built.
-/
private def hoisting (c : α) (depth? : Option Nat) (p : Poly) (type : Expr → Expr) (k : ProofM Expr) : ProofM Expr := do
  let some depth := depth? | k
  let depth := min depth (← read).depth
  unless depth < (← getGoalStackDepth) && !(← read).underDecVar do return ← k
  let key : HoistKey := .ptr (.of c)
  if let some fvarId ← findHoistedDecl? depth key then
    return mkFVar fvarId
  let proof ← withGoalAtDepth depth k
  if proof.isFVar then return proof
  let vars ← getCurrVars
  let (fvarId, idx) ← reserveHoistedDecl depth key (type (← p.denoteExpr (vars[·]!)))
  modify fun s => { s with facts := s.facts.push { depth, idx, proof } }
  return mkFVar fvarId

local macro "declare! " decls:ident a:ident : term =>
  `(do if let some x := (← get).$decls[$a]? then
         return x
       let x := mkFVar (← mkFreshFVarId);
       modify fun s => { s with $decls:ident := (s.$decls).insert $a x };
       return x)

/--
Returns the auxiliary free variable for `a` in the current epoch, creating it if needed.
It is replaced with the value of `a` after the variables are renamed, see `mkProof`.
-/
private def declareInEpoch [BEq α] [Hashable α]
    (proj : EpochDecls → Std.HashMap α Expr) (upd : EpochDecls → Std.HashMap α Expr → EpochDecls)
    (a : α) : ProofM Expr := do
  let epoch := (← read).epoch
  if let some x := (proj (← get).decls[epoch]!)[a]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with decls := s.decls.modify epoch fun ds => upd ds ((proj ds).insert a x) }
  return x

private def mkVarDecl (x : Var) : ProofM Expr :=
  declareInEpoch (·.varDecls) (fun ds m => { ds with varDecls := m }) x

private def mkPolyDecl (p : Poly) : ProofM Expr :=
  declareInEpoch (·.polyDecls) (fun ds m => { ds with polyDecls := m }) p

/-- `Eq.refl p` for the declaration of `p`: the certificate `p = f ...` is checked by definitional equality. -/
private def mkPolyRefl (p : Poly) : ProofM Expr :=
  return mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Int.Internal.Linear.Poly) (← mkPolyDecl p)

private def mkExprDecl (e : Int.Internal.Linear.Expr) : ProofM Expr :=
  declareInEpoch (·.exprDecls) (fun ds m => { ds with exprDecls := m }) e

private def mkRingPolyDecl (p : CommRing.Poly) : ProofM Expr := do
  declare! ringPolyDecls p

private def mkRingExprDecl (e : CommRing.RingExpr) : ProofM Expr := do
  declare! ringExprDecls e

private def toContextExprCore (vars : Array Expr) (type : Expr) : MetaM Expr :=
  if h : 0 < vars.size then
    RArray.toExpr type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr type id (RArray.leaf (mkIntLit 0))

private def ctxType : Expr :=
  mkApp (mkConst ``RArray [Level.zero]) Int.mkType

/--
Returns the outermost enclosing case split, up to `depth`, whose goal has the cutsat variables
`vars` in epoch `epoch`. A variable context with these variables can be declared there.
-/
private def getCtxDepth (depth : Nat) (epoch : Nat) (vars : Array Var) : GoalM Nat := do
  let some maxVar := vars.back? | return 0
  for d in [:depth], (mvarId, goal) in (← get).goalStack do
    if let some vars := (← cutsatExt.getStateCore { goal with mvarId }).getEpochVars? epoch then
      if maxVar < vars.size then return d
  return depth

private def DvdCnstr.get_d_a (c : DvdCnstr) : GoalM (Int × Int) := do
  let d := c.d
  let .add a _ _ := c.p | c.throwUnexpected
  return (d, a)

/-- Similar to `denoteExpr'`, but uses the variables of the current epoch. -/
private def _root_.Int.Internal.Linear.Poly.denoteExprUsingCurrVars (p : Poly) : ProofM Expr := do
  let vars ← getCurrVars
  return (← p.denoteExpr (vars[·]!))

private inductive MulEqProof where
  | const (k : Int) (h : Expr)
  | mulVar (k : Int) (a : Expr) (h : Expr)
  | none

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_cutsat_eq_cnstr_to_proof"] -- forward definition
private opaque EqCnstr.toExprProof (c' : EqCnstr) : ProofM Expr

private partial def mkMulEqProof (x : Var) (a? : Option Expr) (cs : Array (Expr × Int × EqCnstr)) (c' : EqCnstr) : ProofM Expr := do
  let h ← go (← getCurrVars)[x]!
  match h with
  | .const k h =>
    return mkApp6 (mkConst ``Int.Internal.Linear.of_var_eq) (← getContext) (← mkVarDecl x) (toExpr k) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .mulVar k a h =>
    assert! a? == some a
    let y ← getVarOf a
    return mkApp7 (mkConst ``Int.Internal.Linear.of_var_eq_mul) (← getContext) (← mkVarDecl x) (toExpr k) (← mkVarDecl y) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .none =>
    throwError "`grind` internal error, cutsat failed to construct proof for multiplication equality"
where
  goVar (e : Expr) : ProofM MulEqProof := do
    if some e == a? then
      return .mulVar 1 e (mkApp (mkConst ``Int.Internal.Linear.eq_one_mul) e)
    else
      let some (_, k, c) := cs.find? fun (e', _, _) => e' == e | return .none
      let x ← getVarOf e
      let h := mkApp6 (mkConst ``Int.Internal.Linear.var_eq) (← getContext) (← mkVarDecl x) (toExpr k) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
      return .const k h

  go (e : Expr) : ProofM MulEqProof := do
    let_expr HMul.hMul _ _ _ i a b := e | goVar e
    if !(← Structural.isInstHMulInt i) then goVar e else
    let ha ← go a
    if let .const 0 h := ha then
      return .const 0 (mkApp3 (mkConst ``Int.Internal.Linear.mul_eq_zero_left) a b h)
    let hb ← go b
    if let .const 0 h := hb then
      return .const 0 (mkApp3 (mkConst ``Int.Internal.Linear.mul_eq_zero_right) a b h)
    match ha, hb with
    | .const k₁ h₁, .const k₂ h₂ =>
      let k := k₁*k₂
      let h := mkApp8 (mkConst ``Int.Internal.Linear.mul_eq_kk) a b (toExpr k₁) (toExpr k₂) (toExpr k) h₁ h₂ eagerReflBoolTrue
      return .const k h
    | .const k₁ h₁, .mulVar k₂ c h₂ =>
      let k := k₁*k₂
      let h := mkApp9 (mkConst ``Int.Internal.Linear.mul_eq_kkx) a b (toExpr k₁) (toExpr k₂) c (toExpr k) h₁ h₂ eagerReflBoolTrue
      return .mulVar k c h
    | .mulVar k₁ c h₁, .const k₂ h₂ =>
      let k := k₁*k₂
      let h := mkApp9 (mkConst ``Int.Internal.Linear.mul_eq_kxk) a b (toExpr k₁) c (toExpr k₂) (toExpr k) h₁ h₂ eagerReflBoolTrue
      return .mulVar k c h
    | _, _ => return .none

private def mkDivEqProof (k : Int) (y? : Option Var) (c : EqCnstr) (c' : EqCnstr) : ProofM Expr := do
  let .add _ x _ := c'.p | c'.throwUnexpected
  let_expr HDiv.hDiv _ _ _ _ a b := (← getCurrVars)[x]! | c'.throwUnexpected
  let bVar ← getVarOf b
  let h := mkApp6 (mkConst ``Int.Internal.Linear.var_eq) (← getContext) (← mkVarDecl bVar) (toExpr k) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
  if let some y := y? then
    let h := mkApp4 (mkConst ``Int.Internal.Linear.div_eq) a b (toExpr k) h
    return mkApp6 (mkConst ``Int.Internal.Linear.of_var_eq_var) (← getContext) (← mkVarDecl x) (← mkVarDecl y) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  else
    let b' := k
    let some aVal ← getIntValue? a | unreachable!
    let k := aVal / b'
    let h := mkApp6 (mkConst ``Int.Internal.Linear.div_eq') a b (toExpr b') (toExpr k) h eagerReflBoolTrue
    return mkApp6 (mkConst ``Int.Internal.Linear.of_var_eq) (← getContext) (← mkVarDecl x) (toExpr k) (← mkPolyDecl c'.p) eagerReflBoolTrue h

private def mkModEqProof (k : Int) (y? : Option Var) (c : EqCnstr) (c' : EqCnstr) : ProofM Expr := do
  let .add _ x _ := c'.p | c'.throwUnexpected
  let_expr HMod.hMod _ _ _ _ a b := (← getCurrVars)[x]! | c'.throwUnexpected
  let bVar ← getVarOf b
  let h := mkApp6 (mkConst ``Int.Internal.Linear.var_eq) (← getContext) (← mkVarDecl bVar) (toExpr k) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
  if let some y := y? then
    let h := mkApp4 (mkConst ``Int.Internal.Linear.mod_eq) a b (toExpr k) h
    return mkApp6 (mkConst ``Int.Internal.Linear.of_var_eq_var) (← getContext) (← mkVarDecl x) (← mkVarDecl y) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  else
    let b' := k
    let some aVal ← getIntValue? a | unreachable!
    let k := aVal % b'
    let h := mkApp6 (mkConst ``Int.Internal.Linear.mod_eq') a b (toExpr b') (toExpr k) h eagerReflBoolTrue
    return mkApp6 (mkConst ``Int.Internal.Linear.of_var_eq) (← getContext) (← mkVarDecl x) (toExpr k) (← mkPolyDecl c'.p) eagerReflBoolTrue h

private def mkPowEqProof (ka : Int) (ca? : Option EqCnstr) (kb : Nat) (cb? : Option EqCnstr) (c' : EqCnstr) : ProofM Expr := do
  let .add _ x _ := c'.p | c'.throwUnexpected
  let_expr HPow.hPow _ _ _ _ a b := (← getCurrVars)[x]! | c'.throwUnexpected
  let h₁ ← if let some ca := ca? then
    pure <| mkApp6 (mkConst ``Int.Internal.Linear.var_eq) (← getContext) (← mkVarDecl (← getVarOf a)) (toExpr ka) (← mkPolyDecl ca.p) eagerReflBoolTrue (← ca.toExprProof)
  else
    pure <| mkApp2 (mkConst ``Eq.refl [1]) Int.mkType (mkIntLit ka)
  let kbInt := Int.ofNat kb
  let h₂ ← if let some cb := cb? then
    let (b', _) ← mkNatVar b
    pure <| mkApp6 (mkConst ``Int.Internal.Linear.var_eq) (← getContext) (← mkVarDecl (← getVarOf b')) (toExpr kbInt) (← mkPolyDecl cb.p) eagerReflBoolTrue (← cb.toExprProof)
  else
    pure <| mkApp2 (mkConst ``Eq.refl [1]) Int.mkType (mkIntLit kb)
  let k := ka^kb
  let h := mkApp8 (mkConst ``Int.Internal.Linear.pow_eq) a b (toExpr ka) (toExpr kbInt) (toExpr k) h₁ h₂ eagerReflBoolTrue
  return mkApp6 (mkConst ``Int.Internal.Linear.of_var_eq) (← getContext) (← mkVarDecl x) (toExpr k) (← mkPolyDecl c'.p) eagerReflBoolTrue h

set_option compiler.ignoreBorrowAnnotation true in
mutual

@[export lean_cutsat_eq_cnstr_to_proof]
private partial def EqCnstr.toExprProofImpl (c' : EqCnstr) : ProofM Expr := caching c' <| hoisting c' c'.depth? c'.p (mkIntEq · (mkIntLit 0)) do
  trace[grind.debug.lia.proof] "{← c'.pp}"
  match c'.h with
  | .core0 a zero =>
    mkEqProof a zero
  | .core a b p₁ p₂ =>
    let h ← mkEqProof a b
    return mkApp6 (mkConst ``Int.Internal.Linear.eq_of_core_rfl) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) h
  | .coreToInt a b toIntThm lhs rhs =>
    let h := mkApp toIntThm (← mkEqProof a b)
    return mkApp6 (mkConst ``Int.Internal.Linear.eq_norm_expr_rfl) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) h
  | .hyp h lhs rhs =>
    return mkApp6 (mkConst ``Int.Internal.Linear.eq_norm_expr_rfl) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) h
  | .defn e p =>
    let x ← getVarOf e
    return mkApp6 (mkConst ``Int.Internal.Linear.eq_def_rfl) (← getContext) (← mkVarDecl x) (← mkPolyDecl p) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) (← mkEqRefl e)
  | .defnExpr h x e =>
    return mkApp6 (mkConst ``Int.Internal.Linear.eq_def'_rfl) (← getContext) (← mkVarDecl x) (← mkExprDecl e) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Internal.Linear.eq_norm_rfl) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs c.p.getConst
    return mkApp6 (mkConst ``Int.Internal.Linear.eq_coeff) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr k) eagerReflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂  =>
    let a := c₁.p.coeff x
    let b := c₂.p.coeff x
    return mkApp9 (mkConst ``Int.Internal.Linear.eq_eq_subst'_rfl)
      (← getContext) (toExpr a) (toExpr b) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      (← mkPolyRefl c'.p) (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofLeGe c₁ c₂ =>
    return mkApp6 (mkConst ``Int.Internal.Linear.eq_of_le_ge)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofZeroDvd c =>
    return mkApp3 (mkConst ``Int.Internal.Linear.eq_of_zero_dvd)
      (← getContext) (← mkPolyDecl c.p) (← c.toExprProof)
  | .ofDvdDiv c e x t =>
    return mkApp9 (mkConst ``Int.Internal.Linear.eq_of_dvd_ediv)
      (← getContext) (toExpr c.d) (← mkExprDecl e) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (← mkVarDecl x)
      (← mkEqRefl t) eagerReflBoolTrue (← c.toExprProof)
  | .reorder c => withPrevEpoch <| c.toExprProof
  | .commRingNorm c e p =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int_k) (← getRingContext) (← mkRingExprDecl e) (← mkRingPolyDecl p) eagerReflBoolTrue
    return mkApp5 (mkConst ``Int.Internal.Linear.eq_norm_poly) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) h (← c.toExprProof)
  | .defnCommRing e p re rp p' =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int_k) (← getRingContext) (← mkRingExprDecl re) (← mkRingPolyDecl rp) eagerReflBoolTrue
    let x ← getVarOf e
    return mkApp8 (mkConst ``Int.Internal.Linear.eq_def_norm) (← getContext)
      (← mkVarDecl x) (← mkPolyDecl p) (← mkPolyDecl p') (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← mkEqRefl e) h
  | .defnExprCommRing h₁ x e' p re rp p' =>
    let h₂ := mkApp4 (mkConst ``Grind.CommRing.norm_int_k) (← getRingContext) (← mkRingExprDecl re) (← mkRingPolyDecl rp) eagerReflBoolTrue
    return mkApp9 (mkConst ``Int.Internal.Linear.eq_def'_norm) (← getContext) (← mkVarDecl x) (← mkExprDecl e')
      (← mkPolyDecl p) (← mkPolyDecl p') (← mkPolyDecl c'.p) eagerReflBoolTrue h₁ h₂
  | .mul a? cs =>
    let .add _ x _ := c'.p | c'.throwUnexpected
    mkMulEqProof x a? cs c'
  | .div k y? c => mkDivEqProof k y? c c'
  | .mod k y? c => mkModEqProof k y? c c'
  | .pow ka ca? kb cb? => mkPowEqProof ka ca? kb cb? c'

private partial def DvdCnstr.toExprProof (c' : DvdCnstr) : ProofM Expr := caching c' <| hoisting c' c'.depth? c'.p (mkIntDvd (toExpr c'.d)) do
  trace[grind.debug.lia.proof] "{← c'.pp}"
  match c'.h with
  | .core e =>
    mkOfEqTrue (← mkEqTrueProof e)
  | .coreOfNat e thm d a' =>
    let h := mkApp thm (← mkOfEqTrue (← mkEqTrueProof e))
    return mkApp6 (mkConst ``Int.Internal.Linear.dvd_norm_expr) (← getContext) (toExpr (Int.ofNat d)) (← mkExprDecl a') (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .norm c =>
    return mkApp6 (mkConst ``Int.Internal.Linear.dvd_norm) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .elim c =>
    return mkApp7 (mkConst ``Int.Internal.Linear.dvd_elim) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (toExpr c'.d) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let g := c.p.gcdCoeffs c.d
    let g := if c.d < 0 then -g else g
    return mkApp8 (mkConst ``Int.Internal.Linear.dvd_coeff) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (toExpr c'.d) (← mkPolyDecl c'.p) (toExpr g) eagerReflBoolTrue (← c.toExprProof)
  | .bmodCoeffs c a =>
    return mkApp7 (mkConst ``Int.Internal.Linear.dvd_bmod_coeffs) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr a) eagerReflBoolTrue (← c.toExprProof)
  | .solveCombine c₁ c₂ =>
    let (d₁, a₁) ← c₁.get_d_a
    let (d₂, a₂) ← c₂.get_d_a
    let (g, α, β) := gcdExt (a₁*d₂) (a₂*d₁)
    let r := mkApp10 (mkConst ``Int.Internal.Linear.dvd_solve_combine)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (toExpr c₂.d) (← mkPolyDecl c₂.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      (toExpr g) (toExpr α) (toExpr β)
    return mkApp3 r eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .solveElim c₁ c₂ =>
    return mkApp10 (mkConst ``Int.Internal.Linear.dvd_solve_elim)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (toExpr c₂.d) (← mkPolyDecl c₂.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofEqZero c =>
    return mkApp4 (mkConst ``Int.Internal.Linear.dvd_of_eq_zero)
      (← getContext) (toExpr c'.d) (← mkPolyDecl c'.p) (← c.toExprProof)
  | .subst x c₁ c₂ =>
    return mkApp10 (mkConst ``Int.Internal.Linear.eq_dvd_subst)
      (← getContext) (← mkVarDecl x) (← mkPolyDecl c₁.p) (toExpr c₂.d) (← mkPolyDecl c₂.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .cooper₁ s =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    match c₃? with
    | none =>
      let thmName := if left then ``Int.Internal.Linear.cooper_left_split_dvd else ``Int.Internal.Linear.cooper_right_split_dvd
      return mkApp8 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (toExpr s.k) (toExpr c'.d) (← mkPolyDecl c'.p) (← s.toExprProof) eagerReflBoolTrue
    | some c₃ =>
      let thmName := if left then ``Int.Internal.Linear.cooper_dvd_left_split_dvd1 else ``Int.Internal.Linear.cooper_dvd_right_split_dvd1
      return mkApp10 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr s.k) (toExpr c'.d) (← mkPolyDecl c'.p)
        (← s.toExprProof) eagerReflBoolTrue
  | .cooper₂ s =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    let some c₃ := c₃? | throwError "`grind` internal error, unexpected `cooper₂` proof"
    let thmName := if left then ``Int.Internal.Linear.cooper_dvd_left_split_dvd2 else ``Int.Internal.Linear.cooper_dvd_right_split_dvd2
    return mkApp10 (mkConst thmName)
      (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr s.k) (toExpr c'.d) (← mkPolyDecl c'.p)
      (← s.toExprProof) eagerReflBoolTrue
  | .reorder c => withPrevEpoch <| c.toExprProof
  | .commRingNorm c e p =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int_k) (← getRingContext) (← mkRingExprDecl e) (← mkRingPolyDecl p) eagerReflBoolTrue
    return mkApp6 (mkConst ``Int.Internal.Linear.dvd_norm_poly) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) h (← c.toExprProof)

private partial def LeCnstr.toExprProof (c' : LeCnstr) : ProofM Expr := caching c' <| hoisting c' c'.depth? c'.p (mkIntLE · (mkIntLit 0)) do
  trace[grind.debug.lia.proof] "{← c'.pp}"
  match c'.h with
  | .core e =>
    mkOfEqTrue (← mkEqTrueProof e)
  | .coreNeg e p =>
    let h ← mkOfEqFalse (← mkEqFalseProof e)
    return mkApp5 (mkConst ``Int.Internal.Linear.le_neg) (← getContext) (← mkPolyDecl p) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .coreToInt e pos toIntThm lhs rhs =>
    let h ← if pos then pure <| mkOfEqTrueCore e (← mkEqTrueProof e) else pure <| mkOfEqFalseCore e (← mkEqFalseProof e)
    let h := mkApp toIntThm h
    return mkApp6 (mkConst ``Int.Internal.Linear.le_norm_expr_rfl) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) h
  | .coreExpr e pos lhs rhs =>
    if pos then
      let h ← mkOfEqTrue (← mkEqTrueProof e)
      return mkApp6 (mkConst ``Int.Internal.Linear.le_norm_expr_rfl) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) h
    else
      let h ← mkOfEqFalse (← mkEqFalseProof e)
      return mkApp6 (mkConst ``Int.Internal.Linear.not_le_norm_expr) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .ofNatNonneg a =>
    return mkApp (mkConst ``Nat.ToInt.toNat_nonneg) a
  | .hyp h lhs rhs =>
    return mkApp6 (mkConst ``Int.Internal.Linear.le_norm_expr_rfl) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) h
  | .bound h => return h
  | .dec h =>
    return mkFVar h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Internal.Linear.le_norm_rfl) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs'
    return mkApp6 (mkConst ``Int.Internal.Linear.le_coeff) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr (Int.ofNat k)) eagerReflBoolTrue (← c.toExprProof)
  | .combine c₁ c₂ =>
    return mkApp7 (mkConst ``Int.Internal.Linear.le_combine_rfl)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      (← mkPolyRefl c'.p)
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .combineDivCoeffs c₁ c₂ k =>
    let p := c₁.p.mul c₂.p.leadCoeff.natAbs |>.combine (c₂.p.mul c₁.p.leadCoeff.natAbs)
    return mkAppN (mkConst ``Int.Internal.Linear.le_combine_coeff_rfl)
      #[← getContext, ← mkPolyDecl c₁.p, ← mkPolyDecl c₂.p, ← mkPolyDecl p, ← mkPolyDecl c'.p, toExpr k,
        ← mkPolyRefl p, eagerReflBoolTrue, ← mkPolyRefl c'.p, ← c₁.toExprProof, ← c₂.toExprProof]
  | .subst x c₁ c₂ =>
    let a := c₁.p.coeff x
    let thm := if a ≥ 0 then
      mkConst ``Int.Internal.Linear.eq_le_subst_nonneg_rfl
    else
      mkConst ``Int.Internal.Linear.eq_le_subst_nonpos_rfl
    return mkAppN thm
        #[← getContext, ← mkVarDecl x, ← mkPolyDecl c₁.p, ← mkPolyDecl c₂.p, ← mkPolyDecl c'.p,
          eagerReflBoolTrue, ← mkPolyRefl c'.p, ← c₁.toExprProof, ← c₂.toExprProof]
  | .ofLeDiseq c₁ c₂ =>
    return mkApp7 (mkConst ``Int.Internal.Linear.le_of_le_diseq)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .dvdTightMod c₁ c₂ t g =>
    return mkApp10 (mkConst ``Int.Internal.Linear.dvd_le_tight_mod)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p) (toExpr t) (toExpr g)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofDiseqSplit c₁ fvarId h _ =>
    let p₂ := c₁.p.addConst 1
    let hFalse ← withReader ({ · with underDecVar := true }) h.toExprProofCore
    let hNot := mkLambda `h .default (mkIntLE (← p₂.denoteExprUsingCurrVars) (mkIntLit 0)) (hFalse.abstract #[mkFVar fvarId])
    return mkApp7 (mkConst ``Int.Internal.Linear.diseq_split_resolve)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl p₂) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c₁.toExprProof) hNot
  | .cooper s =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    let coeff := if left then p₂.leadCoeff else p₁.leadCoeff
    match c₃? with
    | none =>
      let thmName := if left then ``Int.Internal.Linear.cooper_left_split_ineq else ``Int.Internal.Linear.cooper_right_split_ineq
      return mkApp8 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (toExpr s.k) (toExpr coeff) (← mkPolyDecl c'.p) (← s.toExprProof) eagerReflBoolTrue
    | some c₃ =>
      let thmName := if left then ``Int.Internal.Linear.cooper_dvd_left_split_ineq else ``Int.Internal.Linear.cooper_dvd_right_split_ineq
      return mkApp10 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr s.k) (toExpr coeff) (← mkPolyDecl c'.p) (← s.toExprProof) eagerReflBoolTrue
  | .reorder c => withPrevEpoch <| c.toExprProof
  | .commRingNorm c e p =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int_k) (← getRingContext) (← mkRingExprDecl e) (← mkRingPolyDecl p) eagerReflBoolTrue
    return mkApp5 (mkConst ``Int.Internal.Linear.le_norm_poly) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) h (← c.toExprProof)

private partial def DiseqCnstr.toExprProof (c' : DiseqCnstr) : ProofM Expr := caching c' <| hoisting c' c'.depth? c'.p (fun e => mkNot (mkIntEq e (mkIntLit 0))) do
  match c'.h with
  | .core0 a zero =>
    mkDiseqProof a zero
  | .core a b p₁ p₂ =>
    let h ← mkDiseqProof a b
    return mkApp6 (mkConst ``Int.Internal.Linear.diseq_of_core) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .coreToInt a b toIntThm lhs rhs =>
    let h := mkApp toIntThm (← mkDiseqProof a b)
    return mkApp6 (mkConst ``Int.Internal.Linear.not_eq_norm_expr) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Internal.Linear.diseq_norm_rfl) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (← mkPolyRefl c'.p) (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs c.p.getConst
    return mkApp6 (mkConst ``Int.Internal.Linear.diseq_coeff) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr k) eagerReflBoolTrue (← c.toExprProof)
  | .neg c =>
    return mkApp5 (mkConst ``Int.Internal.Linear.diseq_neg) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂  =>
    return mkAppN (mkConst ``Int.Internal.Linear.eq_diseq_subst_rfl)
      #[← getContext, ← mkVarDecl x, ← mkPolyDecl c₁.p, ← mkPolyDecl c₂.p, ← mkPolyDecl c'.p,
        eagerReflBoolTrue, ← mkPolyRefl c'.p, ← c₁.toExprProof, ← c₂.toExprProof]
  | .reorder c => withPrevEpoch <| c.toExprProof
  | .commRingNorm c e p =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int_k) (← getRingContext) (← mkRingExprDecl e) (← mkRingPolyDecl p) eagerReflBoolTrue
    return mkApp5 (mkConst ``Int.Internal.Linear.diseq_norm_poly) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) h (← c.toExprProof)

private partial def CooperSplit.toExprProof (s : CooperSplit) : ProofM Expr := caching s do
  match s.h with
  | .dec h => return mkFVar h
  | .last hs _ =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    let n := s.pred.numCases
    unless hs.size + 1 == n do
      throwError "`grind` internal error, unexpected number of cases at `CooperSplit` hs.size: {hs.size}, n: {n}, left: {left}\nc₁: {← c₁.pp}\nc₂: {← c₂.pp}\nc₃: {← if let some c₃ := c₃? then c₃.pp else pure ""}"
    let (base, pred) ← match c₃? with
      | none =>
        let thmName := if left then ``Int.Internal.Linear.cooper_left else ``Int.Internal.Linear.cooper_right
        let predName := if left then ``Int.Internal.Linear.cooper_left_split else ``Int.Internal.Linear.cooper_right_split
        let base := mkApp7 (mkConst thmName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (toExpr n)
          eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
        let pred := mkApp3 (mkConst predName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂)
        pure (base, pred)
      | some c₃ =>
        let thmName := if left then ``Int.Internal.Linear.cooper_dvd_left else ``Int.Internal.Linear.cooper_dvd_right
        let predName := if left then ``Int.Internal.Linear.cooper_dvd_left_split else ``Int.Internal.Linear.cooper_dvd_right_split
        let base := mkApp10 (mkConst thmName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr n)
          eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof) (← c₃.toExprProof)
        let pred := mkApp5 (mkConst predName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d)
        pure (base, pred)
    -- `pred` is an expressions of the form `cooper_*_split ...` with type `Nat → Prop`
    let mut k := n
    let mut result := base -- `OrOver k (cooper_*_splti)
    result := mkApp3 (mkConst ``Int.Internal.Linear.orOver_cases) (toExpr (n-1)) pred result
    for (fvarId, c) in hs do
      let type := mkApp pred (toExpr (k-1))
      let h ← withReader ({ · with underDecVar := true }) c.toExprProofCore -- proof of `False`
      -- `hNotCase` is a proof for `¬ pred (k-1)`
      let hNotCase := mkLambda `h .default type (h.abstract #[mkFVar fvarId])
      result := mkApp result hNotCase
      k := k - 1
    -- `result` is now a proof of `p 0`
    return result

private partial def UnsatProof.toExprProofCore (h : UnsatProof) : ProofM Expr := do
  match h with
  | .le c =>
    return mkApp4 (mkConst ``Int.Internal.Linear.le_unsat) (← getContext) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
  | .dvd c =>
    return mkApp5 (mkConst ``Int.Internal.Linear.dvd_unsat) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
  | .eq c =>
    if c.p.isUnsatEq then
      return mkApp4 (mkConst ``Int.Internal.Linear.eq_unsat) (← getContext) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
    else
      let k := c.p.gcdCoeffs'
      return mkApp5 (mkConst ``Int.Internal.Linear.eq_unsat_coeff) (← getContext) (← mkPolyDecl c.p) (toExpr (Int.ofNat k)) eagerReflBoolTrue (← c.toExprProof)
  | .diseq c =>
    return mkApp4 (mkConst ``Int.Internal.Linear.diseq_unsat) (← getContext) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
  | .cooper c₁ c₂ c₃ =>
    let .add c _ _ := c₃.p | c₃.throwUnexpected
    let d := c₃.d
    let (_, α, β) := gcdExt c d
    let h := mkApp7 (mkConst ``Int.Internal.Linear.cooper_unsat) (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr α) (toExpr β)
    return mkApp4 h eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof) (← c₃.toExprProof)

end

/--
Renames the variables used by the proof `h` and the hoisted facts, and replaces the auxiliary free
variables with their values.

The variables, polynomials, and linear expressions (including the `CommRing` ones) are inlined: each
auxiliary free variable is replaced with the ground term of its value after the renaming, in `h` and in
the proofs of the hoisted facts. No `let`-declarations are created for them, so equal values are equal
terms in all proofs, and the kernel can reuse its caches when checking them.
The variable contexts are not inlined: they are declared in enclosing case splits (see `Grind.hoistDecl`),
or in `let`-declarations around `h`.
-/
private def mkProof (h : Expr) (s : ProofM.State) : GoalM Expr := do
  let goalDepth ← getGoalStackDepth
  let mut xs := #[]
  let mut vs := #[]
  let mut epochVars := #[]
  for { varDecls, polyDecls, exprDecls } in s.decls do
    let usedVars  := collectMapVars varDecls collectVar >> collectMapVars polyDecls (·.collectVars) >> collectMapVars exprDecls (·.collectVars) <| {}
    let vars'     := usedVars.toArray
    let varRename := mkVarRename vars'
    for (x, fvar) in varDecls do
      xs := xs.push fvar; vs := vs.push (toExpr (varRename x))
    for (e, fvar) in exprDecls do
      xs := xs.push fvar; vs := vs.push (toExpr (e.renameVars varRename))
    for (p, fvar) in polyDecls do
      xs := xs.push fvar; vs := vs.push (toExpr (p.renameVars varRename))
    epochVars := epochVars.push vars'
  -- Variable contexts that cannot be hoisted.
  let mut locals := #[]
  for ({ depth, epoch }, { fvar }) in s.ctxs do
    -- The variables of the goal at `depth` are renamed to the first ones.
    let numVars := (← getEpochVarsOf (← getGoalAtDepth depth) epoch).size
    let vars := epochVars[epoch]!.filter (· < numVars)
    let atoms := vars.map ((← getEpochVars epoch)[·]!)
    let name := if epoch == s.decls.size - 1 then `ctx else (`ctx).appendIndexAfter epoch
    let ctxDepth ← getCtxDepth depth epoch vars
    if ctxDepth < goalDepth then
      let fvarId ← hoistDecl ctxDepth (.ctx atoms) name ctxType (nondep := false) (front := true) do
        toContextExprCore atoms Int.mkType
      xs := xs.push fvar; vs := vs.push (mkFVar fvarId)
    else
      locals := locals.push (fvar, name, atoms)
  unless s.ringCtxs.isEmpty do
    let some ringId ← getIntRingId?
      | throwError "`grind` internal error, cutsat `CommRing` is not available"
    let ringVars ← CommRing.RingM.run ringId do return (← CommRing.getRingState).vars
    let usedVars  := collectMapVars s.ringPolyDecls (·.collectVars) >> collectMapVars s.ringExprDecls (·.collectVars) <| {}
    let vars'     := usedVars.toArray
    let varRename := mkVarRename vars'
    for (e, fvar) in s.ringExprDecls do
      xs := xs.push fvar; vs := vs.push (toExpr (e.renameVars varRename))
    for (p, fvar) in s.ringPolyDecls do
      xs := xs.push fvar; vs := vs.push (toExpr (p.renameVars varRename))
    for (depth, { fvar }) in s.ringCtxs do
      let numVars := ((← CommRing.ringExt.getStateCore (← getGoalAtDepth depth)).getRing ringId).vars.size
      let atoms := vars'.filter (· < numVars) |>.map (ringVars[·]!)
      if depth < goalDepth then
        let fvarId ← hoistDecl depth (.ctx atoms) `rctx ctxType (nondep := false) (front := true) do
          toContextExprCore atoms Int.mkType
        xs := xs.push fvar; vs := vs.push (mkFVar fvarId)
      else
        locals := locals.push (fvar, `rctx, atoms)
  /-
  Inline the variables, polynomials, and linear expressions, and replace the variable contexts with their
  declarations, in the hoisted facts and in `h`.
  -/
  for { depth, idx, proof } in s.facts do
    setHoistedDeclValue depth idx (proof.replaceFVars xs vs)
  -- The values of the local contexts do not use each other, so they can be abstracted in a single pass.
  let mut h := (h.replaceFVars xs vs).abstract (locals.map (·.1))
  for (_, name, atoms) in locals.reverse do
    h := .letE name ctxType (← toContextExprCore atoms Int.mkType) h (nondep := false)
  return h

def UnsatProof.toExprProof (h : UnsatProof) : GoalM Expr := do
  let numEpochs := (← get').varsHistory.size + 1
  let (h, s) ← h.toExprProofCore.run { epoch := numEpochs - 1, depth := ← getGoalStackDepth } |>.run { decls := Array.replicate numEpochs {} }
  mkProof h s

def setInconsistent (h : UnsatProof) : GoalM Unit := do
  if (← get').caseSplits then
    -- Let the search procedure in `SearchM` resolve the conflict.
    modify' fun s => { s with conflict? := some h }
  else
    let h ← h.toExprProof
    closeGoal h

/-!
A cutsat proof may depend on decision variables.
We collect them and perform non chronological backtracking.
-/

open CollectDecVars
mutual
partial def EqCnstr.collectDecVars (c' : EqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core0 .. | .core .. | .defn .. | .defnExpr ..
  | .defnCommRing .. | .defnExprCommRing .. | .coreToInt .. | .hyp .. => return () -- Equalities coming from the core never contain cutsat decision variables
  | .commRingNorm c .. | .reorder c | .norm c | .divCoeffs c | .div _ _ c | .mod _ _ c => c.collectDecVars
  | .ofZeroDvd c | .ofDvdDiv c .. => c.collectDecVars
  | .subst _ c₁ c₂ | .ofLeGe c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars
  | .mul _ cs => cs.forM fun (_, _, c) => c.collectDecVars
  | .pow _ ca? _ cb? => ca?.forM (·.collectDecVars); cb?.forM (·.collectDecVars)

partial def CooperSplit.collectDecVars (s : CooperSplit) : CollectDecVarsM Unit := do unless (← alreadyVisited s) do
  s.pred.c₁.collectDecVars
  s.pred.c₂.collectDecVars
  if let some c₃ := s.pred.c₃? then
    c₃.collectDecVars
  match s.h with
  | .dec h => markAsFound h
  | .last (decVars := decVars) .. => decVars.forM markAsFound

partial def DvdCnstr.collectDecVars (c' : DvdCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core _  | .coreOfNat .. => return ()
  | .cooper₁ c | .cooper₂ c
  | .commRingNorm c .. | .reorder c | .norm c | .elim c | .divCoeffs c | .bmodCoeffs c _ => c.collectDecVars
  | .ofEqZero c => c.collectDecVars
  | .solveCombine c₁ c₂ | .solveElim c₁ c₂ | .subst _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

partial def LeCnstr.collectDecVars (c' : LeCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core .. | .coreNeg .. | .coreToInt .. | .coreExpr .. | .ofNatNonneg .. | .hyp .. | .bound .. => return ()
  | .dec h => markAsFound h
  | .commRingNorm c .. | .reorder c | .cooper c
  | .norm c | .divCoeffs c => c.collectDecVars
  | .dvdTightMod c₁ c₂ _ _
  | .combine c₁ c₂ | .combineDivCoeffs c₁ c₂ _
  | .subst _ c₁ c₂ | .ofLeDiseq c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars
  | .ofDiseqSplit (decVars := decVars) .. => decVars.forM markAsFound

partial def DiseqCnstr.collectDecVars (c' : DiseqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core0 .. | .core .. | .coreToInt .. => return () -- Disequalities coming from the core never contain cutsat decision variables
  | .commRingNorm c .. | .reorder c | .norm c | .divCoeffs c | .neg c => c.collectDecVars
  | .subst _ c₁ c₂  => c₁.collectDecVars; c₂.collectDecVars

end

def UnsatProof.collectDecVars (h : UnsatProof) : CollectDecVarsM Unit := do
  match h with
  | .le c | .dvd c | .eq c | .diseq c => c.collectDecVars
  | .cooper c₁ c₂ c₃ => c₁.collectDecVars; c₂.collectDecVars; c₃.collectDecVars

end Lean.Meta.Grind.Arith.Cutsat
