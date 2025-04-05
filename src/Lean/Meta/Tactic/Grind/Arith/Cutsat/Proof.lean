/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat

namespace Lean.Meta.Grind.Arith.Cutsat

deriving instance Hashable for Int.Linear.Expr
deriving instance Hashable for Int.OfNat.Expr

structure ProofM.State where
  cache       : Std.HashMap UInt64 Expr := {}
  polyMap     : Std.HashMap Poly Expr := {}
  exprMap     : Std.HashMap Int.Linear.Expr Expr := {}
  natExprMap  : Std.HashMap Int.OfNat.Expr Expr := {}

structure ProofM.Context where
  ctx : Expr
  foreignCtxs : Std.HashMap ForeignType Expr

/-- Auxiliary monad for constructing cutsat proofs. -/
abbrev ProofM := ReaderT ProofM.Context (StateRefT ProofM.State GoalM)

/-- Returns a Lean expression representing the variable context used to construct cutsat proofs. -/
private abbrev getContext : ProofM Expr := do
  return (← read).ctx

private abbrev getForeignContext (type : ForeignType) : ProofM Expr := do
  let some ctx := (← read).foreignCtxs[type]? | throwError "`grind` internal error, unexpected type while constructing cutsat proof"
  return ctx

private abbrev caching (c : α) (k : ProofM Expr) : ProofM Expr := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  if let some h := (← get).cache[addr]? then
    return h
  else
    let h ← k
    modify fun s => { s with cache := s.cache.insert addr h }
    return h

def mkPolyDecl (p : Poly) : ProofM Expr := do
  if let some x := (← get).polyMap[p]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with polyMap := s.polyMap.insert p x }
  return x

def mkExprDecl (e : Int.Linear.Expr) : ProofM Expr := do
  if let some x := (← get).exprMap[e]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with exprMap := s.exprMap.insert e x }
  return x

def mkNatExprDecl (e : Int.OfNat.Expr) : ProofM Expr := do
  if let some x := (← get).natExprMap[e]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with natExprMap := s.natExprMap.insert e x }
  return x

private def mkDiseqProof (a b : Expr) : GoalM Expr := do
 let some h ← mkDiseqProof? a b
   | throwError "internal `grind` error, failed to build disequality proof for{indentExpr a}\nand{indentExpr b}"
  return h

private def mkLetOfMap {_ : Hashable α} {_ : BEq α} (m : Std.HashMap α Expr) (e : Expr)
    (varPrefix : Name) (varType : Expr) (toExpr : α → Expr) : GoalM Expr := do
  if m.isEmpty then
    return e
  else
    let as := m.toArray
    let mut e := e.abstract <| as.map (·.2)
    let mut i := as.size
    for (p, _) in as.reverse do
      e := mkLet (varPrefix.appendIndexAfter i) varType (toExpr p) e
      i := i - 1
    return e

private def toContextExprCore (vars : PArray Expr) (type : Expr) : Expr :=
  if h : 0 < vars.size then
    RArray.toExpr type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr type id (RArray.leaf (mkIntLit 0))

private def toContextExpr : GoalM Expr := do
  return toContextExprCore (← getVars) (mkConst ``Int)

private def withForeignContexts (k : Std.HashMap ForeignType Expr → GoalM α) : GoalM α := do
  go 1 (← get').foreignVars.toList {}
where
  go (i : Nat) (ctxs : List (ForeignType × PArray Expr)) (r : Std.HashMap ForeignType Expr) : GoalM α := do
    match ctxs with
    | [] => k r
    | (type, ctx) :: ctxs =>
      let typeExpr := type.denoteType
      let ctxExpr := toContextExprCore ctx typeExpr
      withLetDecl ((`ctx).appendIndexAfter i) (mkApp (mkConst ``RArray) typeExpr) ctxExpr fun ctx => do
        go (i+1) ctxs (r.insert type ctx)

private def getLetCtxVars : ProofM (Array Expr) := do
  let mut r := #[(← getContext)]
  for (_, ctx) in (← read).foreignCtxs do
    r := r.push ctx
  return r

private abbrev withProofContext (x : ProofM Expr) : GoalM Expr := do
  withLetDecl `ctx (mkApp (mkConst ``RArray) (mkConst ``Int)) (← toContextExpr) fun ctx =>
  withForeignContexts fun foreignCtxs =>
    go { ctx, foreignCtxs } |>.run' {}
where
  go : ProofM Expr := do
    let h ← x
    let h ← mkLetOfMap (← get).polyMap h `p (mkConst ``Int.Linear.Poly) toExpr
    let h ← mkLetOfMap (← get).exprMap h `e (mkConst ``Int.Linear.Expr) toExpr
    let h ← mkLetOfMap (← get).natExprMap h `a (mkConst ``Int.OfNat.Expr) toExpr
    mkLetFVars (← getLetCtxVars) h

private def DvdCnstr.get_d_a (c : DvdCnstr) : GoalM (Int × Int) := do
  let d := c.d
  let .add a _ _ := c.p | c.throwUnexpected
  return (d, a)

mutual
partial def EqCnstr.toExprProof (c' : EqCnstr) : ProofM Expr := caching c' do
  trace[grind.debug.cutsat.proof] "{← c'.pp}"
  match c'.h with
  | .core0 a zero =>
    mkEqProof a zero
  | .core a b p₁ p₂ =>
    let h ← mkEqProof a b
    return mkApp6 (mkConst ``Int.Linear.eq_of_core) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c'.p) reflBoolTrue h
  | .coreNat a b lhs rhs lhs' rhs' =>
    let ctx ← getForeignContext .nat
    let h := mkApp4 (mkConst ``Int.OfNat.of_eq) ctx (← mkNatExprDecl lhs) (← mkNatExprDecl rhs) (← mkEqProof a b)
    return mkApp6 (mkConst ``Int.Linear.eq_norm_expr) (← getContext) (← mkExprDecl lhs') (← mkExprDecl rhs') (← mkPolyDecl c'.p) reflBoolTrue h
  | .defn e p =>
    let some x := (← get').varMap.find? { expr := e } | throwError "`grind` internal error, missing cutsat variable{indentExpr e}"
    return mkApp6 (mkConst ``Int.Linear.eq_def) (← getContext) (toExpr x) (← mkPolyDecl p) (← mkPolyDecl c'.p) reflBoolTrue (← mkEqRefl e)
  | .norm c =>
    return mkApp5 (mkConst ``Int.Linear.eq_norm) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) reflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs c.p.getConst
    return mkApp6 (mkConst ``Int.Linear.eq_coeff) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr k) reflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂  =>
    return mkApp8 (mkConst ``Int.Linear.eq_eq_subst)
      (← getContext) (toExpr x) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofLeGe c₁ c₂ =>
    return mkApp6 (mkConst ``Int.Linear.eq_of_le_ge)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)

partial def DvdCnstr.toExprProof (c' : DvdCnstr) : ProofM Expr := caching c' do
  trace[grind.debug.cutsat.proof] "{← c'.pp}"
  match c'.h with
  | .core e =>
    mkOfEqTrue (← mkEqTrueProof e)
  | .coreNat e d b b' =>
    let ctx ← getForeignContext .nat
    let h := mkApp4 (mkConst ``Int.OfNat.of_dvd) ctx (toExpr d) (← mkNatExprDecl b) (mkOfEqTrueCore e (← mkEqTrueProof e))
    return mkApp6 (mkConst ``Int.Linear.dvd_norm_expr) (← getContext) (toExpr (Int.ofNat d)) (← mkExprDecl b') (← mkPolyDecl c'.p) reflBoolTrue h
  | .norm c =>
    return mkApp6 (mkConst ``Int.Linear.dvd_norm) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) reflBoolTrue (← c.toExprProof)
  | .elim c =>
    return mkApp7 (mkConst ``Int.Linear.dvd_elim) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (toExpr c'.d) (← mkPolyDecl c'.p) reflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let g := c.p.gcdCoeffs c.d
    let g := if c.d < 0 then -g else g
    return mkApp8 (mkConst ``Int.Linear.dvd_coeff) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) (toExpr c'.d) (← mkPolyDecl c'.p) (toExpr g) reflBoolTrue (← c.toExprProof)
  | .solveCombine c₁ c₂ =>
    let (d₁, a₁) ← c₁.get_d_a
    let (d₂, a₂) ← c₂.get_d_a
    let (g, α, β) := gcdExt (a₁*d₂) (a₂*d₁)
    let r := mkApp10 (mkConst ``Int.Linear.dvd_solve_combine)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (toExpr c₂.d) (← mkPolyDecl c₂.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      (toExpr g) (toExpr α) (toExpr β)
    return mkApp3 r reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .solveElim c₁ c₂ =>
    return mkApp10 (mkConst ``Int.Linear.dvd_solve_elim)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (toExpr c₂.d) (← mkPolyDecl c₂.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofEq x c =>
    return mkApp7 (mkConst ``Int.Linear.dvd_of_eq)
      (← getContext) (toExpr x) (← mkPolyDecl c.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      reflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂ =>
    return mkApp10 (mkConst ``Int.Linear.eq_dvd_subst)
      (← getContext) (toExpr x) (← mkPolyDecl c₁.p) (toExpr c₂.d) (← mkPolyDecl c₂.p) (toExpr c'.d) (← mkPolyDecl c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .cooper₁ s =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    match c₃? with
    | none =>
      let thmName := if left then ``Int.Linear.cooper_left_split_dvd else ``Int.Linear.cooper_right_split_dvd
      return mkApp8 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (toExpr s.k) (toExpr c'.d) (← mkPolyDecl c'.p) (← s.toExprProof) reflBoolTrue
    | some c₃ =>
      let thmName := if left then ``Int.Linear.cooper_dvd_left_split_dvd1 else ``Int.Linear.cooper_dvd_right_split_dvd1
      return mkApp10 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr s.k) (toExpr c'.d) (← mkPolyDecl c'.p)
        (← s.toExprProof) reflBoolTrue
  | .cooper₂ s =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    let some c₃ := c₃? | throwError "`grind` internal error, unexpected `cooper₂` proof"
    let thmName := if left then ``Int.Linear.cooper_dvd_left_split_dvd2 else ``Int.Linear.cooper_dvd_right_split_dvd2
    return mkApp10 (mkConst thmName)
      (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr s.k) (toExpr c'.d) (← mkPolyDecl c'.p)
      (← s.toExprProof) reflBoolTrue

partial def LeCnstr.toExprProof (c' : LeCnstr) : ProofM Expr := caching c' do
  trace[grind.debug.cutsat.proof] "{← c'.pp}"
  match c'.h with
  | .core e =>
    mkOfEqTrue (← mkEqTrueProof e)
  | .coreNeg e p =>
    let h ← mkOfEqFalse (← mkEqFalseProof e)
    return mkApp5 (mkConst ``Int.Linear.le_neg) (← getContext) (← mkPolyDecl p) (← mkPolyDecl c'.p) reflBoolTrue h
  | .coreNat e lhs rhs lhs' rhs' =>
    let ctx ← getForeignContext .nat
    let h := mkApp4 (mkConst ``Int.OfNat.of_le) ctx (← mkNatExprDecl lhs) (← mkNatExprDecl rhs) (mkOfEqTrueCore e (← mkEqTrueProof e))
    return mkApp6 (mkConst ``Int.Linear.le_norm_expr) (← getContext) (← mkExprDecl lhs') (← mkExprDecl rhs') (← mkPolyDecl c'.p) reflBoolTrue h
  | .denoteAsIntNonneg rhs rhs' =>
    let ctx ← getForeignContext .nat
    let h := mkApp2 (mkConst ``Int.OfNat.Expr.denoteAsInt_nonneg) ctx (toExpr rhs)
    return mkApp6 (mkConst ``Int.Linear.le_norm_expr) (← getContext) (← mkExprDecl (.num 0)) (← mkExprDecl rhs') (← mkPolyDecl c'.p) reflBoolTrue h
  | .coreNatNeg e lhs rhs lhs' rhs' =>
    let ctx ← getForeignContext .nat
    let h := mkApp4 (mkConst ``Int.OfNat.of_not_le) ctx (← mkNatExprDecl lhs) (← mkNatExprDecl rhs) (mkOfEqFalseCore e (← mkEqFalseProof e))
    return mkApp6 (mkConst ``Int.Linear.not_le_norm_expr) (← getContext) (← mkExprDecl lhs') (← mkExprDecl rhs') (← mkPolyDecl c'.p) reflBoolTrue h
  | .dec h =>
    return mkFVar h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Linear.le_norm) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) reflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs'
    return mkApp6 (mkConst ``Int.Linear.le_coeff) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr (Int.ofNat k)) reflBoolTrue (← c.toExprProof)
  | .combine c₁ c₂ =>
    return mkApp7 (mkConst ``Int.Linear.le_combine)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      reflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .combineDivCoeffs c₁ c₂ k =>
    return mkApp8 (mkConst ``Int.Linear.le_combine_coeff)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p) (toExpr k)
      reflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .subst x c₁ c₂ =>
    let a := c₁.p.coeff x
    let thm := if a ≥ 0 then
      mkConst ``Int.Linear.eq_le_subst_nonneg
    else
      mkConst ``Int.Linear.eq_le_subst_nonpos
    return mkApp8 thm
        (← getContext) (toExpr x) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
        reflBoolTrue
        (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofLeDiseq c₁ c₂ =>
    return mkApp7 (mkConst ``Int.Linear.le_of_le_diseq)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .dvdTight c₁ c₂ =>
    return mkApp8 (mkConst ``Int.Linear.dvd_le_tight)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .negDvdTight c₁ c₂ =>
    return mkApp8 (mkConst ``Int.Linear.dvd_neg_le_tight)
      (← getContext) (toExpr c₁.d) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .ofDiseqSplit c₁ fvarId h _ =>
    let p₂ := c₁.p.addConst 1
    let hFalse ← h.toExprProofCore
    let hNot := mkLambda `h .default (mkIntLE (← p₂.denoteExpr') (mkIntLit 0)) (hFalse.abstract #[mkFVar fvarId])
    return mkApp7 (mkConst ``Int.Linear.diseq_split_resolve)
      (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl p₂) (← mkPolyDecl c'.p) reflBoolTrue (← c₁.toExprProof) hNot
  | .cooper s =>
    let { c₁, c₂, c₃?, left } := s.pred
    let p₁ := c₁.p
    let p₂ := c₂.p
    let coeff := if left then p₂.leadCoeff else p₁.leadCoeff
    match c₃? with
    | none =>
      let thmName := if left then ``Int.Linear.cooper_left_split_ineq else ``Int.Linear.cooper_right_split_ineq
      return mkApp8 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (toExpr s.k) (toExpr coeff) (← mkPolyDecl c'.p) (← s.toExprProof) reflBoolTrue
    | some c₃ =>
      let thmName := if left then ``Int.Linear.cooper_dvd_left_split_ineq else ``Int.Linear.cooper_dvd_right_split_ineq
      return mkApp10 (mkConst thmName)
        (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr s.k) (toExpr coeff) (← mkPolyDecl c'.p) (← s.toExprProof) reflBoolTrue

partial def DiseqCnstr.toExprProof (c' : DiseqCnstr) : ProofM Expr := caching c' do
  trace[grind.debug.cutsat.proof] "{← c'.pp}"
  match c'.h with
  | .core0 a zero =>
    mkDiseqProof a zero
  | .core a b p₁ p₂ =>
    let h ← mkDiseqProof a b
    return mkApp6 (mkConst ``Int.Linear.diseq_of_core) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c'.p) reflBoolTrue h
  | .coreNat a b lhs rhs lhs' rhs' =>
    let ctx ← getForeignContext .nat
    let h := mkApp4 (mkConst ``Int.OfNat.of_not_eq) ctx (← mkNatExprDecl lhs) (← mkNatExprDecl rhs) (← mkDiseqProof a b)
    return mkApp6 (mkConst ``Int.Linear.not_eq_norm_expr) (← getContext) (← mkExprDecl lhs') (← mkExprDecl rhs') (← mkPolyDecl c'.p) reflBoolTrue h
  | .norm c =>
    return mkApp5 (mkConst ``Int.Linear.diseq_norm) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) reflBoolTrue (← c.toExprProof)
  | .divCoeffs c =>
    let k := c.p.gcdCoeffs c.p.getConst
    return mkApp6 (mkConst ``Int.Linear.diseq_coeff) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr k) reflBoolTrue (← c.toExprProof)
  | .neg c =>
    return mkApp5 (mkConst ``Int.Linear.diseq_neg) (← getContext) (← mkPolyDecl c.p) (← mkPolyDecl c'.p) reflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂  =>
    return mkApp8 (mkConst ``Int.Linear.eq_diseq_subst)
      (← getContext) (toExpr x) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)

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
          reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
        let pred := mkApp3 (mkConst predName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂)
        pure (base, pred)
      | some c₃ =>
        let thmName := if left then ``Int.Linear.cooper_dvd_left else ``Int.Linear.cooper_dvd_right
        let predName := if left then ``Int.Linear.cooper_dvd_left_split else ``Int.Linear.cooper_dvd_right_split
        let base := mkApp10 (mkConst thmName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr n)
          reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof) (← c₃.toExprProof)
        let pred := mkApp5 (mkConst predName) (← getContext) (← mkPolyDecl p₁) (← mkPolyDecl p₂) (← mkPolyDecl c₃.p) (toExpr c₃.d)
        pure (base, pred)
    -- `pred` is an expressions of the form `cooper_*_split ...` with type `Nat → Prop`
    let mut k := n
    let mut result := base -- `OrOver k (cooper_*_splti)
    trace[grind.debug.cutsat.proof] "orOver_cases {n}"
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
  trace[grind.debug.cutsat.proof] "{← h.pp}"
  match h with
  | .le c =>
    return mkApp4 (mkConst ``Int.Linear.le_unsat) (← getContext) (← mkPolyDecl c.p) reflBoolTrue (← c.toExprProof)
  | .dvd c =>
    return mkApp5 (mkConst ``Int.Linear.dvd_unsat) (← getContext) (toExpr c.d) (← mkPolyDecl c.p) reflBoolTrue (← c.toExprProof)
  | .eq c =>
    if c.p.isUnsatEq then
      return mkApp4 (mkConst ``Int.Linear.eq_unsat) (← getContext) (← mkPolyDecl c.p) reflBoolTrue (← c.toExprProof)
    else
      let k := c.p.gcdCoeffs'
      return mkApp5 (mkConst ``Int.Linear.eq_unsat_coeff) (← getContext) (← mkPolyDecl c.p) (toExpr (Int.ofNat k)) reflBoolTrue (← c.toExprProof)
  | .diseq c =>
    return mkApp4 (mkConst ``Int.Linear.diseq_unsat) (← getContext) (← mkPolyDecl c.p) reflBoolTrue (← c.toExprProof)
  | .cooper c₁ c₂ c₃ =>
    let .add c _ _ := c₃.p | c₃.throwUnexpected
    let d := c₃.d
    let (_, α, β) := gcdExt c d
    let h := mkApp7 (mkConst ``Int.Linear.cooper_unsat) (← getContext) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c₃.p) (toExpr c₃.d) (toExpr α) (toExpr β)
    return mkApp4 h reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof) (← c₃.toExprProof)

end

def UnsatProof.toExprProof (h : UnsatProof) : GoalM Expr := do
  withProofContext do h.toExprProofCore

def setInconsistent (h : UnsatProof) : GoalM Unit := do
  trace[grind.debug.cutsat.conflict] "setInconsistent [{← inconsistent}]: {← h.pp}"
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

structure CollectDecVars.State where
  visited : Std.HashSet UInt64 := {}
  found : FVarIdSet := {}
abbrev CollectDecVarsM := ReaderT FVarIdSet (StateM CollectDecVars.State)

private def alreadyVisited (c : α) : CollectDecVarsM Bool := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  if (← get).visited.contains addr then return true
  modify fun s => { s with visited := s.visited.insert addr }
  return false

private def markAsFound (fvarId : FVarId) : CollectDecVarsM Unit := do
  modify fun s => { s with found := s.found.insert fvarId }

mutual
partial def EqCnstr.collectDecVars (c' : EqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core0 .. | .core .. | .coreNat .. | .defn .. => return () -- Equalities coming from the core never contain cutsat decision variables
  | .norm c | .divCoeffs c => c.collectDecVars
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
  | .core _ | .coreNat .. => return ()
  | .cooper₁ c | .cooper₂ c
  | .norm c | .elim c | .divCoeffs c | .ofEq _ c => c.collectDecVars
  | .solveCombine c₁ c₂ | .solveElim c₁ c₂ | .subst _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

partial def LeCnstr.collectDecVars (c' : LeCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core .. | .coreNeg .. | .coreNat .. | .coreNatNeg .. | .denoteAsIntNonneg .. => return ()
  | .dec h => markAsFound h
  | .cooper c | .norm c | .divCoeffs c => c.collectDecVars
  | .dvdTight c₁ c₂ | .negDvdTight c₁ c₂
  | .combine c₁ c₂ | .combineDivCoeffs c₁ c₂ _
  | .subst _ c₁ c₂ | .ofLeDiseq c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars
  | .ofDiseqSplit (decVars := decVars) .. => decVars.forM markAsFound

partial def DiseqCnstr.collectDecVars (c' : DiseqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core0 .. | .core .. | .coreNat .. => return () -- Disequalities coming from the core never contain cutsat decision variables
  | .norm c | .divCoeffs c | .neg c => c.collectDecVars
  | .subst _ c₁ c₂  => c₁.collectDecVars; c₂.collectDecVars

end

def UnsatProof.collectDecVars (h : UnsatProof) : CollectDecVarsM Unit := do
  match h with
  | .le c | .dvd c | .eq c | .diseq c => c.collectDecVars
  | .cooper c₁ c₂ c₃ => c₁.collectDecVars; c₂.collectDecVars; c₃.collectDecVars

abbrev CollectDecVarsM.run (x : CollectDecVarsM Unit) (decVars : FVarIdSet) : FVarIdSet :=
  let (_, s) := x decVars |>.run {}
  s.found

end Lean.Meta.Grind.Arith.Cutsat
