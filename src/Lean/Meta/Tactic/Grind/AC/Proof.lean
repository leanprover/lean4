/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.AC.Util
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.ProofUtil
import Lean.Meta.Tactic.Grind.AC.ToExpr
import Lean.Meta.Tactic.Grind.AC.VarRename
public section
namespace Lean.Meta.Grind.AC
open Lean.Grind

structure ProofM.State where
  cache      : Std.HashMap UInt64 Expr := {}
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

private def mkDupPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type (← getContext) s.assocInst (← getIdempotentInst)

private def toContextExpr (vars : Array Expr) : ACM Expr := do
  let s ← getStruct
  if h : 0 < vars.size then
    RArray.toExpr (mkApp (mkConst ``PLift [s.u]) s.type) id (RArray.ofFn (vars[·]) h)
  else unreachable!

private def mkContext (h : Expr) : ProofM Expr := do
  let s ← getStruct
  let mut usedVars     :=
    collectMapVars (← get).seqDecls (·.collectVars) >>
    collectMapVars (← get).exprDecls (·.collectVars) >>
    (if (← hasNeutral) then (collectVar 0) else id) <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := (← getStruct).vars
  let up           := mkApp (mkConst ``PLift.up [s.u]) s.type
  let vars         := vars'.map fun x => mkApp up vars[x]!
  let h := mkLetOfMap (← get).seqDecls h `p (mkConst ``Grind.AC.Seq) fun p => toExpr <| p.renameVars varRename
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
    let h ← mkDupPrefix ``AC.diseq_erase_dup
    return mkApp6 h (← mkSeqDecl c₁.lhs) (← mkSeqDecl c₁.rhs) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← c₁.toExprProof)
  | _ => throwError "NIY"

def DiseqCnstr.setUnsat (c : DiseqCnstr) : ACM Unit := do
  let h ← withProofContext do
    return mkApp4 (← mkPrefix ``AC.diseq_unsat) (← mkSeqDecl c.lhs) (← mkSeqDecl c.rhs) eagerReflBoolTrue (← c.toExprProof)
  closeGoal h

end Lean.Meta.Grind.AC
