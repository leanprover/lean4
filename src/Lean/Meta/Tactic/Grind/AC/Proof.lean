/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.AC.Util
import Lean.Meta.Tactic.Grind.AC.ToExpr
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

private def mkAPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [.succ s.u]) s.type (← getContext) s.assocInst

private def mkACPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [.succ s.u]) s.type (← getContext) s.assocInst (← getCommInst)

private def mkAIPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [.succ s.u]) s.type (← getContext) s.assocInst (← getNeutralInst)

private def mkACIPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp5 (mkConst declName [.succ s.u]) s.type (← getContext) s.assocInst (← getCommInst) (← getNeutralInst)

private def mkDupPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [.succ s.u]) s.type (← getContext) s.assocInst (← getIdempotentInst)



end Lean.Meta.Grind.AC
