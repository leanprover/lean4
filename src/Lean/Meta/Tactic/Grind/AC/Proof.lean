/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.AC.Util
import Lean.Data.RArray
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.ProofUtil
import Lean.Meta.Tactic.Grind.AC.ToExpr
import Lean.Meta.Tactic.Grind.AC.VarRename
import Init.Data.Nat.Order
import Init.Data.Order.Lemmas
public section
namespace Lean.Meta.Grind.AC
open Lean.Grind

structure ProofM.State where
  cache      : Std.HashMap UInt64 Expr := {}
  varDecls   : Std.HashMap AC.Var Expr := {}
  exprDecls  : Std.HashMap AC.Expr Expr := {}
  seqDecls   : Std.HashMap AC.Seq Expr := {}

structure ProofM.Context where
  ctx   : Expr

abbrev ProofM := ReaderT ProofM.Context (StateRefT ProofM.State ACM)

/-- Returns a Lean expression representing the variable context used to construct `AC` proof steps. -/
private def getContext : ProofM Expr := do
  return (← read).ctx

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

private def mkVarDecl (x : AC.Var) : ProofM Expr := do
  declare! varDecls x

private def mkSeqDecl (s : AC.Seq) : ProofM Expr := do
  declare! seqDecls s

private def mkExprDecl (e : AC.Expr) : ProofM Expr := do
  declare! exprDecls e

private def getCommInst : ACM Expr := do
  let some inst := (← getStruct).commInst? | throwError "`grind` internal error, `{(← getStruct).op}` is not commutative"
  return inst

private def getIdempotentInst : ACM Expr := do
  let some inst := (← getStruct).idempotentInst? | throwError "`grind` internal error, `{(← getStruct).op}` is not idempotent"
  return inst

private def getNeutralInst : ACM Expr := do
  let some inst := (← getStruct).neutralInst? | throwError "`grind` internal error, `{(← getStruct).op}` does not have a neutral element"
  return inst

private def mkPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp2 (mkConst declName [s.u]) s.type (← getContext)

private def mkAPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type (← getContext) s.assocInst

private def mkACPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type (← getContext) s.assocInst (← getCommInst)

private def mkAIPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type (← getContext) s.assocInst (← getNeutralInst)

private def mkACIPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp5 (mkConst declName [s.u]) s.type (← getContext) s.assocInst (← getCommInst) (← getNeutralInst)

private def mkADPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type (← getContext) s.assocInst (← getIdempotentInst)

private def mkACDPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp5 (mkConst declName [s.u]) s.type (← getContext) s.assocInst (← getCommInst) (← getIdempotentInst)

private def toContextExpr (vars : Array Expr) : ACM Expr := do
  let s ← getStruct
  if h : 0 < vars.size then
    RArray.toExpr (mkApp (mkConst ``PLift [s.u]) s.type) id (RArray.ofFn (vars[·]) h)
  else unreachable!

private def mkContext (h : Expr) : ProofM Expr := do
  let s ← getStruct
  let varDecls := (← get).varDecls
  let mut usedVars     :=
    collectMapVars varDecls collectVar >>
    collectMapVars (← get).seqDecls (·.collectVars) >>
    collectMapVars (← get).exprDecls (·.collectVars) >>
    (if (← hasNeutral) then (collectVar 0) else id) <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := (← getStruct).vars
  let varFVars     := vars'.map fun x => varDecls[x]?.getD default
  let varIdsAsExpr := List.range vars'.size |>.toArray |>.map toExpr
  let h := h.replaceFVars varFVars varIdsAsExpr
  let up           := mkApp (mkConst ``PLift.up [s.u]) s.type
  let vars         := vars'.map fun x => mkApp up vars[x]!
  let h := mkLetOfMap (← get).seqDecls h `s (mkConst ``Grind.AC.Seq) fun p => toExpr <| p.renameVars varRename
  let h := mkLetOfMap (← get).exprDecls h `e (mkConst ``Grind.AC.Expr) fun e => toExpr <| e.renameVars varRename
  let h := h.abstract #[(← read).ctx]
  if h.hasLooseBVars then
    let ctxType := mkApp (mkConst ``AC.Context [s.u]) s.type
    let ctxVal := mkApp3 (mkConst ``AC.Context.mk [s.u]) s.type (← toContextExpr vars) s.op
    return .letE `ctx ctxType ctxVal h (nondep := false)
  else
    return h

private abbrev withProofContext (x : ProofM Expr) : ACM Expr := do
  let ctx := mkFVar (← mkFreshFVarId)
  go { ctx } |>.run' {}
where
  go : ProofM Expr := do
    mkContext (← x)

partial def EqCnstr.toExprProof (c : EqCnstr) : ProofM Expr := do caching c do
  match c.h with
  | .core a b lhs rhs =>
    let h ← match (← isCommutative), (← hasNeutral) with
      | false, false => mkAPrefix ``AC.eq_norm_a
      | false, true  => mkAIPrefix ``AC.eq_norm_ai
      | true,  false => mkACPrefix ``AC.eq_norm_ac
      | true,  true  => mkACIPrefix ``AC.eq_norm_aci
    return mkApp6 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← mkEqProof a b)
  | .refl s =>
    let h ← mkPrefix ``AC.refl
    return mkApp h (← mkSeqDecl s)
  | .erase_dup c₁ =>
    let h ← mkADPrefix ``AC.eq_erase_dup
    return mkApp6 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← c₁.toExprProof)
  | .erase_dup_rhs c₁ =>
    let h ← mkADPrefix ``AC.eq_erase_dup_rhs
    return mkApp5 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← c₁.toExprProof)
  | .erase0 c₁ =>
    let h ← mkAIPrefix ``AC.eq_erase0
    return mkApp6 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← c₁.toExprProof)
  | .erase0_rhs c₁ =>
    let h ← mkAIPrefix ``AC.eq_erase0_rhs
    return mkApp5 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← c₁.toExprProof)
  | .simp_exact isLhs c₁ c₂ =>
    let h ← mkPrefix <| if isLhs then ``AC.eq_simp_lhs_exact else ``AC.eq_simp_rhs_exact
    let o := if isLhs then c₂.rhs else c₂.lhs
    return mkApp5 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl o) (← c₁.toExprProof) (← c₂.toExprProof)
  | .simp_prefix isLhs tail c₁ c₂ =>
    let h ← mkAPrefix <| if isLhs then ``AC.eq_simp_lhs_prefix else ``AC.eq_simp_rhs_prefix
    let s' := if isLhs then c.lhs else c.rhs
    return mkApp9 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl tail) (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl s')
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .simp_suffix isLhs head c₁ c₂ =>
    let h ← mkAPrefix <| if isLhs then ``AC.eq_simp_lhs_suffix else ``AC.eq_simp_rhs_suffix
    let s' := if isLhs then c.lhs else c.rhs
    return mkApp9 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl head) (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl s')
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .simp_middle isLhs head tail c₁ c₂ =>
    let h ← mkAPrefix <| if isLhs then ``AC.eq_simp_lhs_middle else ``AC.eq_simp_rhs_middle
    let s' := if isLhs then c.lhs else c.rhs
    return mkApp10 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl head) (← mkSeqDecl tail) (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl s')
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .simp_ac isLhs s c₁ c₂ =>
    let h ← mkACPrefix <| if isLhs then ``AC.eq_simp_lhs_ac else ``AC.eq_simp_rhs_ac
    let s' := if isLhs then c.lhs else c.rhs
    return mkApp9 h (← mkSeqDecl s) (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl s')
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .swap c =>
    let h ← mkPrefix ``AC.eq_orient
    return mkApp3 h (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) (← c.toExprProof)
  | .superpose_ac r₁ common r₂ c₁ c₂  =>
    let h ← mkACPrefix ``AC.superpose_ac
    let h := mkApp9 h (← mkSeqDecl r₁) (← mkSeqDecl common) (← mkSeqDecl r₂) (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs)
        (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs)
    return mkApp3 h eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .superpose p common s c₁ c₂ =>
    let h ← mkAPrefix ``AC.superpose
    let h := mkApp9 h (← mkSeqDecl p) (← mkSeqDecl common) (← mkSeqDecl s) (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs)
        (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs)
    return mkApp3 h eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .superpose_ac_idempotent x c₁ =>
    let h ← mkACDPrefix ``AC.superpose_ac_idempotent
    let h := mkApp4 h (← mkVarDecl x) (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.rhs)
    return mkApp2 h eagerReflBoolTrue (← c₁.toExprProof)
  | .superpose_head_idempotent x c₁ =>
    let h ← mkADPrefix ``AC.superpose_head_idempotent
    let h := mkApp4 h (← mkVarDecl x) (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.rhs)
    return mkApp2 h eagerReflBoolTrue (← c₁.toExprProof)
  | .superpose_tail_idempotent x c₁ =>
    let h ← mkADPrefix ``AC.superpose_tail_idempotent
    let h := mkApp4 h (← mkVarDecl x) (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.rhs)
    return mkApp2 h eagerReflBoolTrue (← c₁.toExprProof)

partial def DiseqCnstr.toExprProof (c : DiseqCnstr) : ProofM Expr := do caching c do
  match c.h with
  | .core a b lhs rhs =>
    let h ← match (← isCommutative), (← hasNeutral) with
      | false, false => mkAPrefix ``AC.diseq_norm_a
      | false, true  => mkAIPrefix ``AC.diseq_norm_ai
      | true,  false => mkACPrefix ``AC.diseq_norm_ac
      | true,  true  => mkACIPrefix ``AC.diseq_norm_aci
    return mkApp6 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← mkDiseqProof a b)
  | .erase_dup c₁ =>
    let h ← mkADPrefix ``AC.diseq_erase_dup
    return mkApp6 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← c₁.toExprProof)
  | .erase0 c₁ =>
    let h ← mkAIPrefix ``AC.diseq_erase0
    return mkApp6 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← c₁.toExprProof)
  | .simp_exact isLhs c₁ c₂ =>
    let h ← mkPrefix <| if isLhs then ``AC.diseq_simp_lhs_exact else ``AC.diseq_simp_rhs_exact
    let o := if isLhs then c₂.rhs else c₂.lhs
    return mkApp5 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl o) (← c₁.toExprProof) (← c₂.toExprProof)
  | .simp_prefix isLhs tail c₁ c₂ =>
    let h ← mkAPrefix <| if isLhs then ``AC.diseq_simp_lhs_prefix else ``AC.diseq_simp_rhs_prefix
    let s' := if isLhs then c.lhs else c.rhs
    return mkApp9 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl tail) (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl s')
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .simp_suffix isLhs head c₁ c₂ =>
    let h ← mkAPrefix <| if isLhs then ``AC.diseq_simp_lhs_suffix else ``AC.diseq_simp_rhs_suffix
    let s' := if isLhs then c.lhs else c.rhs
    return mkApp9 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl head) (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl s')
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .simp_middle isLhs head tail c₁ c₂ =>
    let h ← mkAPrefix <| if isLhs then ``AC.diseq_simp_lhs_middle else ``AC.diseq_simp_rhs_middle
    let s' := if isLhs then c.lhs else c.rhs
    return mkApp10 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl head) (← mkSeqDecl tail) (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl s')
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .simp_ac isLhs s c₁ c₂ =>
    let h ← mkACPrefix <| if isLhs then ``AC.diseq_simp_lhs_ac else ``AC.diseq_simp_rhs_ac
    let s' := if isLhs then c.lhs else c.rhs
    return mkApp9 h (← mkSeqDecl s) (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c₂.lhs) (← mkSeqDecl c₂.rhs) (← mkSeqDecl s')
      eagerReflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)

def DiseqCnstr.setUnsat (c : DiseqCnstr) : ACM Unit := do
  let h ← withProofContext do
    return mkApp4 (← mkPrefix ``AC.diseq_unsat) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← c.toExprProof)
  closeGoal h

def mkExprEqSeqProof (e : AC.Expr) (c : EqCnstr) : ProofM Expr := do
  let h ← match (← isCommutative), (← hasNeutral) with
    | false, false => mkAPrefix ``AC.norm_a
    | false, true  => mkAIPrefix ``AC.norm_ai
    | true,  false => mkACPrefix ``AC.norm_ac
    | true,  true  => mkACIPrefix ``AC.norm_aci
  let h₁ := mkApp3 h (← mkExprDecl e) (← mkSeqDecl c.lhs) eagerReflBoolTrue
  let h₂ ← c.toExprProof
  let h ← mkPrefix ``AC.eq_expr_seq_seq
  return mkApp5 h (← mkExprDecl e) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) h₁ h₂

/--
Asserts `a = b`, where
- `ea` is `a`s reification
- `eb` is `b`s reification
- `ca` is a proof for `sa = s` where `norm ea = sa`
- `cb` is a proof for `sb = s` where `norm eb = sb`
-/
def propagateEq (a b : Expr) (ea eb : AC.Expr) (ca cb : EqCnstr) : ACM Unit := do
  assert! ca.rhs == cb.rhs
  let h ← withProofContext do
    let h₁ ← mkExprEqSeqProof ea ca
    let h₂ ← mkExprEqSeqProof eb cb
    let h ← mkPrefix ``AC.imp_eq
    return mkApp5 h (← mkExprDecl ea) (← mkExprDecl eb) (← mkSeqDecl ca.rhs) h₁ h₂
  let s ← getStruct
  let eq := mkApp3 (mkConst ``Eq [s.u]) s.type a b
  pushEq a b <| mkExpectedPropHint h eq

end Lean.Meta.Grind.AC
