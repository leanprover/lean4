/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Grind.Ring.Poly
public import Lean.Meta.Tactic.Grind.Diseq
public import Lean.Meta.Tactic.Grind.Arith.Util
public import Lean.Meta.Tactic.Grind.Arith.ProofUtil
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Util
public import Lean.Meta.Tactic.Grind.Arith.VarRename
import Lean.Meta.Tactic.Grind.Arith.Cutsat.VarRename
import Lean.Meta.Tactic.Grind.Arith.CommRing.VarRename
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof

public section

namespace Lean.Meta.Grind.Arith.Cutsat

deriving instance Hashable for Int.Linear.Expr

/--
State for the cutsat proof construction monad.

The final proof may reference only a small subset of the cutsat variables.
Thus, we normalize the variables and remove any that are unused from the context.
The variable order must be preserved, as the cutsat auxiliary theorems assume the polynomials are ordered.

Another complication is that cutsat may reorder variables during the search.
This is why we maintain two fields: `vars` and `vars'`.

We create auxiliary free variables for variables, polynomials, and expressions.
Cutsat also uses the ring solver to normalize nonlinear polynomials.

Remark: after normalization variable declarations are expanded. We do not create let-declarations for them
since they are just a numeral.

Remark: if cutsat did not reorder variables during the search, then the prime variables and declarations
are not used.

Remark: recall that the `.reorder` proof objects are delimiters for indicating whether regular variables and
declarations or the prime ones should be used.
-/
structure ProofM.State where
  /-- Cache for visited cutsat proof terms. The key is the pointer address. -/
  cache         : Std.HashMap UInt64 Expr := {}
  /-- Map from used variables to (temporary) free variable. -/
  varDecls      : Std.HashMap Var Expr := {}
  /-- Map from used polynomials to free variable. -/
  polyDecls     : Std.HashMap Poly Expr := {}
  /-- Map from used cutsat expressions to free variable. -/
  exprDecls     : Std.HashMap Int.Linear.Expr Expr := {}
  /-- Map from used variables (before reordering) to (temporary) free variable. -/
  varDecls'     : Std.HashMap Var Expr := {}
  /-- Map from used polynomials (before reordering) to free variable. -/
  polyDecls'    : Std.HashMap Poly Expr := {}
  /-- Map from used cutsat expressions (before reordering) to free variable. -/
  exprDecls'    : Std.HashMap Int.Linear.Expr Expr := {}
  /-- Map from used ring polynomials to free variable. -/
  ringPolyDecls : Std.HashMap CommRing.Poly Expr := {}
  /-- Map from used ring expressions to free variable. -/
  ringExprDecls : Std.HashMap CommRing.RingExpr Expr := {}

structure ProofM.Context where
  ctx       : Expr
  /-- Variables before reordering -/
  ctx'      : Expr
  ringCtx   : Expr
  /--
  `unordered` is `true` if we entered a `.reorder c` justification. The variables in `c` and
  its dependencies are unordered.
  -/
  unordered : Bool := false

/-- Auxiliary monad for constructing cutsat proofs. -/
abbrev ProofM := ReaderT ProofM.Context (StateRefT ProofM.State GoalM)

/-- Returns a Lean expression representing the variable context used to construct cutsat proofs. -/
private def getContext : ProofM Expr := do
  return (← read).ctx

/--
Execute `k` with `unordered := true`, and the unordered variable context.
We use this combinator to process `.reorder c` justifications.
-/
private abbrev withUnordered (k : ProofM α) : ProofM α := do
  withReader (fun c => { c with ctx := c.ctx', unordered := true }) k

/--
Returns the mapping from expressions to cutsat variables.
These are variables before the renaming them.
-/
private def getVarMap : ProofM (PHashMap ExprPtr Var) := do
  if (← read).unordered then
    return (← get').varMap'
  else
    return (← get').varMap

private abbrev caching (c : α) (k : ProofM Expr) : ProofM Expr := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  if let some h := (← get).cache[addr]? then
    return h
  else
    let h ← k
    modify fun s => { s with cache := s.cache.insert addr h }
    return h

local macro "declare! " decls:ident a:ident : term =>
  `(do if let some x := (← get).$decls[$a]? then
         return x
       let x := mkFVar (← mkFreshFVarId);
       modify fun s => { s with $decls:ident := (s.$decls).insert $a x };
       return x)

private def mkVarDecl (x : Var) : ProofM Expr := do
  if (← read).unordered then
    declare! varDecls' x
  else
    declare! varDecls x

private def mkPolyDecl (p : Poly) : ProofM Expr := do
  if (← read).unordered then
    declare! polyDecls' p
  else
    declare! polyDecls p

private def mkExprDecl (e : Int.Linear.Expr) : ProofM Expr := do
  if (← read).unordered then
    declare! exprDecls' e
  else
    declare! exprDecls e

private def mkRingPolyDecl (p : CommRing.Poly) : ProofM Expr := do
  declare! ringPolyDecls p

private def mkRingExprDecl (e : CommRing.RingExpr) : ProofM Expr := do
  declare! ringExprDecls e

private def toContextExprCore (vars : Array Expr) (type : Expr) : MetaM Expr :=
  if h : 0 < vars.size then
    RArray.toExpr type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr type id (RArray.leaf (mkIntLit 0))

-- Remark: the `prime` flag is used just to distinguish variables before/after reordering.
-- Recall that we keep two contexts. The "prime" one is the one **before** reordering.
private def mkContext
    (ctxVar : Expr) (prime : Bool) (vars : PArray Expr) (varDecls : Std.HashMap Var Expr) (polyDecls : Std.HashMap Poly Expr) (exprDecls : Std.HashMap Int.Linear.Expr Expr)
    (h : Expr) : GoalM Expr := do
  let usedVars     := collectMapVars varDecls collectVar >> collectMapVars polyDecls (·.collectVars) >> collectMapVars exprDecls (·.collectVars) <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := vars'.map fun x => vars[x]!
  let varFVars     := vars'.map fun x => varDecls[x]?.getD default
  let varIdsAsExpr := List.range vars'.size |>.toArray |>.map toExpr
  let h := h.replaceFVars varFVars varIdsAsExpr
  let h := mkLetOfMap exprDecls h (cond prime `e' `e) (mkConst ``Int.Linear.Expr) fun e => toExpr <| e.renameVars varRename
  let h := mkLetOfMap polyDecls h (cond prime `p' `p) (mkConst ``Int.Linear.Poly) fun p => toExpr <| p.renameVars varRename
  let h := h.abstract #[ctxVar]
  if h.hasLooseBVars then
    let ctxType := mkApp (mkConst ``RArray [levelZero]) Int.mkType
    let ctxVal ← toContextExprCore vars Int.mkType
    return .letE (cond prime `ctx' `ctx) ctxType ctxVal h (nondep := false)
  else
    return h

private def mkRingContext (h : Expr) : ProofM Expr := do
  unless (← get').usedCommRing do return h
  let some ringId ← getIntRingId? | return h
  let vars ← CommRing.RingM.run ringId do return (← CommRing.getRing).vars
  let usedVars     := collectMapVars (← get).ringPolyDecls (·.collectVars) >> collectMapVars (← get).ringExprDecls (·.collectVars) <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := vars'.map fun x => vars[x]!
  let h := mkLetOfMap (← get).ringExprDecls h `re (mkConst ``Grind.CommRing.Expr) fun e => toExpr <| e.renameVars varRename
  let h := mkLetOfMap (← get).ringPolyDecls h `rp (mkConst ``Grind.CommRing.Poly) fun p => toExpr <| p.renameVars varRename
  let h := h.abstract #[(← read).ringCtx]
  if h.hasLooseBVars then
    let ctxType := mkApp (mkConst ``RArray [levelZero]) Int.mkType
    let ctxVal ← toContextExprCore vars Int.mkType
    return .letE `rctx ctxType ctxVal h (nondep := false)
  else
    return h

private abbrev withProofContext (x : ProofM Expr) : GoalM Expr := do
  let ctx := mkFVar (← mkFreshFVarId)
  let ctx' := mkFVar (← mkFreshFVarId)
  let ringCtx := mkFVar (← mkFreshFVarId)
  go { ctx, ctx', ringCtx } |>.run' {}
where
  go : ProofM Expr := do
    let h ← x
    let h ← mkRingContext h
    let h ← mkContext (← read).ctx' (prime := true) (← get').vars' (← get).varDecls' (← get).polyDecls' (← get).exprDecls' h
    mkContext (← read).ctx (prime := false) (← get').vars (← get).varDecls (← get).polyDecls (← get).exprDecls h

/--
Returns a Lean expression representing the auxiliary `CommRing` variable context needed for normalizing
nonlinear polynomials.
-/
private abbrev getRingContext : ProofM Expr := do
  return (← read).ringCtx

private def DvdCnstr.get_d_a (c : DvdCnstr) : GoalM (Int × Int) := do
  let d := c.d
  let .add a _ _ := c.p | c.throwUnexpected
  return (d, a)

/--
Similar to `denoteExpr'`, but takes into account the `unordered` flag in the `ProofM` context.
Recall that if `unordered` is `true`, we should use `vars'`
-/
private def _root_.Int.Linear.Poly.denoteExprUsingCurrVars (p : Poly) : ProofM Expr := do
  let vars ← if (← read).unordered then pure (← get').vars' else getVars
  return (← p.denoteExpr (vars[·]!))

mutual
partial def EqCnstr.toExprProof (c' : EqCnstr) : ProofM Expr := caching c' do
  trace[grind.debug.cutsat.proof] "{← c'.pp}"
  match c'.h with
  | .core0 a zero =>
    mkEqProof a zero
  | .core a b p₁ p₂ =>
    let h ← mkEqProof a b
    return mkApp6 (mkConst ``Int.Linear.eq_of_core) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .coreToInt a b toIntThm lhs rhs =>
    let h := mkApp toIntThm (← mkEqProof a b)
    return mkApp6 (mkConst ``Int.Linear.eq_norm_expr) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .defn e p =>
    let some x := (← getVarMap).find? { expr := e } | throwError "`grind` internal error, missing cutsat variable{indentExpr e}"
    return mkApp6 (mkConst ``Int.Linear.eq_def) (← getContext) (← mkVarDecl x) (← mkPolyDecl p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← mkEqRefl e)
  | .defnNat h x e =>
    return mkApp6 (mkConst ``Int.Linear.eq_def') (← getContext) (← mkVarDecl x) (← mkExprDecl e) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Linear.eq_norm) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs c.p.getConst
    return mkApp6 (mkConst ``Int.Linear.eq_coeff) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr k) eagerReflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂  =>
    let a := c₁.p.coeff x
    let b := c₂.p.coeff x
    return mkApp9 (mkConst ``Int.Linear.eq_eq_subst')
      (← getContext) (toExpr a) (toExpr b) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofLeGe c₁ c₂ =>
    return mkApp6 (mkConst ``Int.Linear.eq_of_le_ge)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .reorder c => withUnordered <| c.toExprProof
  | .commRingNorm c e p =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int) (← getRingContext) (← mkRingExprDecl e) (← mkRingPolyDecl p) eagerReflBoolTrue
    return mkApp5 (mkConst ``Int.Linear.eq_norm_poly) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) h (← c.toExprProof)
  | .defnCommRing e p re rp p' =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int) (← getRingContext) (← mkRingExprDecl re) (← mkRingPolyDecl rp) eagerReflBoolTrue
    let some x := (← getVarMap).find? { expr := e } | throwError "`grind` internal error, missing cutsat variable{indentExpr e}"
    return mkApp8 (mkConst ``Int.Linear.eq_def_norm) (← getContext)
      (← mkVarDecl x) (← mkPolyDecl p) (← mkPolyDecl p') (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← mkEqRefl e) h
  | .defnNatCommRing h₁ x e' p re rp p' =>
    let h₂ := mkApp4 (mkConst ``Grind.CommRing.norm_int) (← getRingContext) (← mkRingExprDecl re) (← mkRingPolyDecl rp) eagerReflBoolTrue
    return mkApp9 (mkConst ``Int.Linear.eq_def'_norm) (← getContext) (← mkVarDecl x) (← mkExprDecl e')
      (← mkPolyDecl p) (← mkPolyDecl p') (← mkPolyDecl c'.p) eagerReflBoolTrue h₁ h₂

partial def DvdCnstr.toExprProof (c' : DvdCnstr) : ProofM Expr := caching c' do
  trace[grind.debug.cutsat.proof] "{← c'.pp}"
  match c'.h with
  | .core e =>
    mkOfEqTrue (← mkEqTrueProof e)
  | .coreOfNat e thm d a' =>
    let h := mkApp thm (← mkOfEqTrue (← mkEqTrueProof e))
    return mkApp6 (mkConst ``Int.Linear.dvd_norm_expr) (← getContext) (toExpr (Int.ofNat d)) (← mkExprDecl a') (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .norm c =>
    return mkApp6 (mkConst ``Int.Linear.dvd_norm) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .elim c =>
    return mkApp7 (mkConst ``Int.Linear.dvd_elim) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (toExpr c'.d) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let g := c.p.gcdCoeffs c.d
    let g := if c.d < 0 then -g else g
    return mkApp8 (mkConst ``Int.Linear.dvd_coeff) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (toExpr c'.d) (← mkPolyDecl c'.p) (toExpr g) eagerReflBoolTrue (← c.toExprProof)
  | .solveCombine c₁ c₂ =>
    let (d₁, a₁) ← c₁.get_d_a
    let (d₂, a₂) ← c₂.get_d_a
    let (g, α, β) := gcdExt (a₁*d₂) (a₂*d₁)
    let r := mkApp10 (mkConst ``Int.Linear.dvd_solve_combine)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (toExpr c₂.d) (← mkPolyDecl c₂.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      (toExpr g) (toExpr α) (toExpr β)
    return mkApp3 r eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .solveElim c₁ c₂ =>
    return mkApp10 (mkConst ``Int.Linear.dvd_solve_elim)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (toExpr c₂.d) (← mkPolyDecl c₂.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofEq x c =>
    return mkApp7 (mkConst ``Int.Linear.dvd_of_eq)
      (← getContext) (← mkVarDecl x) (← mkPolyDecl c.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂ =>
    return mkApp10 (mkConst ``Int.Linear.eq_dvd_subst)
      (← getContext) (← mkVarDecl x) (← mkPolyDecl c₁.p) (toExpr c₂.d) (← mkPolyDecl c₂.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .cooper₁ s =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    match c₃? with
    | none =>
      let thmName := if left then ``Int.Linear.cooper_left_split_dvd else ``Int.Linear.cooper_right_split_dvd
      return mkApp8 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (toExpr s.k) (toExpr c'.d) (← mkPolyDecl c'.p) (← s.toExprProof) eagerReflBoolTrue
    | some c₃ =>
      let thmName := if left then ``Int.Linear.cooper_dvd_left_split_dvd1 else ``Int.Linear.cooper_dvd_right_split_dvd1
      return mkApp10 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr s.k) (toExpr c'.d) (← mkPolyDecl c'.p)
        (← s.toExprProof) eagerReflBoolTrue
  | .cooper₂ s =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    let some c₃ := c₃? | throwError "`grind` internal error, unexpected `cooper₂` proof"
    let thmName := if left then ``Int.Linear.cooper_dvd_left_split_dvd2 else ``Int.Linear.cooper_dvd_right_split_dvd2
    return mkApp10 (mkConst thmName)
      (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr s.k) (toExpr c'.d) (← mkPolyDecl c'.p)
      (← s.toExprProof) eagerReflBoolTrue
  | .reorder c => withUnordered <| c.toExprProof
  | .commRingNorm c e p =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int) (← getRingContext) (← mkRingExprDecl e) (← mkRingPolyDecl p) eagerReflBoolTrue
    return mkApp6 (mkConst ``Int.Linear.dvd_norm_poly) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) h (← c.toExprProof)

partial def LeCnstr.toExprProof (c' : LeCnstr) : ProofM Expr := caching c' do
  trace[grind.debug.cutsat.proof] "{← c'.pp}"
  match c'.h with
  | .core e =>
    mkOfEqTrue (← mkEqTrueProof e)
  | .coreNeg e p =>
    let h ← mkOfEqFalse (← mkEqFalseProof e)
    return mkApp5 (mkConst ``Int.Linear.le_neg) (← getContext) (← mkPolyDecl p) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .coreToInt e pos toIntThm lhs rhs =>
    let h ← if pos then pure <| mkOfEqTrueCore e (← mkEqTrueProof e) else pure <| mkOfEqFalseCore e (← mkEqFalseProof e)
    let h := mkApp toIntThm h
    return mkApp6 (mkConst ``Int.Linear.le_norm_expr) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .ofNatNonneg a =>
    return mkApp (mkConst ``Nat.ToInt.toNat_nonneg) a
  | .bound h => return h
  | .dec h =>
    return mkFVar h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Linear.le_norm) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs'
    return mkApp6 (mkConst ``Int.Linear.le_coeff) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr (Int.ofNat k)) eagerReflBoolTrue (← c.toExprProof)
  | .combine c₁ c₂ =>
    return mkApp7 (mkConst ``Int.Linear.le_combine)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      eagerReflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .combineDivCoeffs c₁ c₂ k =>
    return mkApp8 (mkConst ``Int.Linear.le_combine_coeff)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p) (toExpr k)
      eagerReflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .subst x c₁ c₂ =>
    let a := c₁.p.coeff x
    let thm := if a ≥ 0 then
      mkConst ``Int.Linear.eq_le_subst_nonneg
    else
      mkConst ``Int.Linear.eq_le_subst_nonpos
    return mkApp8 thm
        (← getContext) (← mkVarDecl x) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
        eagerReflBoolTrue
        (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofLeDiseq c₁ c₂ =>
    return mkApp7 (mkConst ``Int.Linear.le_of_le_diseq)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .dvdTight c₁ c₂ =>
    return mkApp8 (mkConst ``Int.Linear.dvd_le_tight)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .negDvdTight c₁ c₂ =>
    return mkApp8 (mkConst ``Int.Linear.dvd_neg_le_tight)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofDiseqSplit c₁ fvarId h _ =>
    let p₂ := c₁.p.addConst 1
    let hFalse ← h.toExprProofCore
    let hNot := mkLambda `h .default (mkIntLE (← p₂.denoteExprUsingCurrVars) (mkIntLit 0)) (hFalse.abstract #[mkFVar fvarId])
    return mkApp7 (mkConst ``Int.Linear.diseq_split_resolve)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl p₂) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c₁.toExprProof) hNot
  | .cooper s =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    let coeff := if left then p₂.leadCoeff else p₁.leadCoeff
    match c₃? with
    | none =>
      let thmName := if left then ``Int.Linear.cooper_left_split_ineq else ``Int.Linear.cooper_right_split_ineq
      return mkApp8 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (toExpr s.k) (toExpr coeff) (← mkPolyDecl c'.p) (← s.toExprProof) eagerReflBoolTrue
    | some c₃ =>
      let thmName := if left then ``Int.Linear.cooper_dvd_left_split_ineq else ``Int.Linear.cooper_dvd_right_split_ineq
      return mkApp10 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr s.k) (toExpr coeff) (← mkPolyDecl c'.p) (← s.toExprProof) eagerReflBoolTrue
  | .reorder c => withUnordered <| c.toExprProof
  | .commRingNorm c e p =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int) (← getRingContext) (← mkRingExprDecl e) (← mkRingPolyDecl p) eagerReflBoolTrue
    return mkApp5 (mkConst ``Int.Linear.le_norm_poly) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) h (← c.toExprProof)

partial def DiseqCnstr.toExprProof (c' : DiseqCnstr) : ProofM Expr := caching c' do
  match c'.h with
  | .core0 a zero =>
    mkDiseqProof a zero
  | .core a b p₁ p₂ =>
    let h ← mkDiseqProof a b
    return mkApp6 (mkConst ``Int.Linear.diseq_of_core) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .coreToInt a b toIntThm lhs rhs =>
    let h := mkApp toIntThm (← mkDiseqProof a b)
    return mkApp6 (mkConst ``Int.Linear.not_eq_norm_expr) (← getContext) (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) eagerReflBoolTrue h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Linear.diseq_norm) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs c.p.getConst
    return mkApp6 (mkConst ``Int.Linear.diseq_coeff) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr k) eagerReflBoolTrue (← c.toExprProof)
  | .neg c =>
    return mkApp5 (mkConst ``Int.Linear.diseq_neg) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) eagerReflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂  =>
    return mkApp8 (mkConst ``Int.Linear.eq_diseq_subst)
      (← getContext) (← mkVarDecl x) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .reorder c => withUnordered <| c.toExprProof
  | .commRingNorm c e p =>
    let h := mkApp4 (mkConst ``Grind.CommRing.norm_int) (← getRingContext) (← mkRingExprDecl e) (← mkRingPolyDecl p) eagerReflBoolTrue
    return mkApp5 (mkConst ``Int.Linear.diseq_norm_poly) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) h (← c.toExprProof)

partial def CooperSplit.toExprProof (s : CooperSplit) : ProofM Expr := caching s do
  match s.h with
  | .dec h => return mkFVar h
  | .last hs _ =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    let n := s.pred.numCases
    unless hs.size + 1 == n do
      throwError "`grind` internal error, unexpected number of cases at `CopperSplit` hs.size: {hs.size}, n: {n}, left: {left}\nc₁: {← c₁.pp}\nc₂: {← c₂.pp}\nc₃: {← if let some c₃ := c₃? then c₃.pp else pure ""}"
    let (base, pred) ← match c₃? with
      | none =>
        let thmName := if left then ``Int.Linear.cooper_left else ``Int.Linear.cooper_right
        let predName := if left then ``Int.Linear.cooper_left_split else ``Int.Linear.cooper_right_split
        let base := mkApp7 (mkConst thmName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (toExpr n)
          eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
        let pred := mkApp3 (mkConst predName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂)
        pure (base, pred)
      | some c₃ =>
        let thmName := if left then ``Int.Linear.cooper_dvd_left else ``Int.Linear.cooper_dvd_right
        let predName := if left then ``Int.Linear.cooper_dvd_left_split else ``Int.Linear.cooper_dvd_right_split
        let base := mkApp10 (mkConst thmName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr n)
          eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof) (← c₃.toExprProof)
        let pred := mkApp5 (mkConst predName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d)
        pure (base, pred)
    -- `pred` is an expressions of the form `cooper_*_split ...` with type `Nat → Prop`
    let mut k := n
    let mut result := base -- `OrOver k (cooper_*_splti)
    result := mkApp3 (mkConst ``Int.Linear.orOver_cases) (toExpr (n-1)) pred result
    for (fvarId, c) in hs do
      let type := mkApp pred (toExpr (k-1))
      let h ← c.toExprProofCore -- proof of `False`
      -- `hNotCase` is a proof for `¬ pred (k-1)`
      let hNotCase := mkLambda `h .default type (h.abstract #[mkFVar fvarId])
      result := mkApp result hNotCase
      k := k - 1
    -- `result` is now a proof of `p 0`
    return result

partial def UnsatProof.toExprProofCore (h : UnsatProof) : ProofM Expr := do
  match h with
  | .le c =>
    return mkApp4 (mkConst ``Int.Linear.le_unsat) (← getContext) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
  | .dvd c =>
    return mkApp5 (mkConst ``Int.Linear.dvd_unsat) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
  | .eq c =>
    if c.p.isUnsatEq then
      return mkApp4 (mkConst ``Int.Linear.eq_unsat) (← getContext) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
    else
      let k := c.p.gcdCoeffs'
      return mkApp5 (mkConst ``Int.Linear.eq_unsat_coeff) (← getContext) (← mkPolyDecl c.p) (toExpr (Int.ofNat k)) eagerReflBoolTrue (← c.toExprProof)
  | .diseq c =>
    return mkApp4 (mkConst ``Int.Linear.diseq_unsat) (← getContext) (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
  | .cooper c₁ c₂ c₃ =>
    let .add c _ _ := c₃.p | c₃.throwUnexpected
    let d := c₃.d
    let (_, α, β) := gcdExt c d
    let h := mkApp7 (mkConst ``Int.Linear.cooper_unsat) (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr α) (toExpr β)
    return mkApp4 h eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof) (← c₃.toExprProof)

end

def UnsatProof.toExprProof (h : UnsatProof) : GoalM Expr := do
  withProofContext do h.toExprProofCore

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
  | .core0 .. | .core .. | .defn .. | .defnNat ..
  | .defnCommRing .. | .defnNatCommRing .. | .coreToInt .. => return () -- Equalities coming from the core never contain cutsat decision variables
  | .commRingNorm c .. | .reorder c | .norm c | .divCoeffs c => c.collectDecVars
  | .subst _ c₁ c₂ | .ofLeGe c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

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
  | .commRingNorm c .. | .reorder c | .norm c | .elim c | .divCoeffs c | .ofEq _ c => c.collectDecVars
  | .solveCombine c₁ c₂ | .solveElim c₁ c₂ | .subst _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

partial def LeCnstr.collectDecVars (c' : LeCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core .. | .coreNeg .. | .coreToInt .. | .ofNatNonneg .. | .bound .. => return ()
  | .dec h => markAsFound h
  | .commRingNorm c .. | .reorder c | .cooper c
  | .norm c | .divCoeffs c => c.collectDecVars
  | .dvdTight c₁ c₂ | .negDvdTight c₁ c₂
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
