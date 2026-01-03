/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SimpM
public import Lean.Meta.Sym.SimpFun
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.DiscrTree
namespace Lean.Meta.Sym.Simp
open Grind

public def mkTheoremFromDecl (declName : Name) : MetaM Theorem := do
  let (pattern, rhs) ← mkEqPatternFromDecl declName
  return { expr := mkConst declName, pattern, rhs }

/--
Creates proof term for a rewriting step.
Handles both constant expressions (common case, avoids `instantiateLevelParams`)
and general expressions.
-/
def mkValue (expr : Expr) (pattern : Pattern) (result : MatchUnifyResult) : Expr :=
  if let .const declName [] := expr then
    mkAppN (mkConst declName result.us) result.args
  else
    mkAppN (expr.instantiateLevelParams pattern.levelParams result.us) result.args

/--
Tries to rewrite `e` using the given theorem.
-/
-- **TODO**: Define `Step` result?
public def Theorem.rewrite? (thm : Theorem) (e : Expr) : SimpM (Option Result) := do
  if let some result ← thm.pattern.match? e then
    let proof? := some <| mkValue thm.expr thm.pattern result
    let rhs    := thm.rhs.instantiateLevelParams thm.pattern.levelParams result.us
    let rhs    ← shareCommonInc rhs
    let expr   ← instantiateRevBetaS rhs result.args
    return some { expr, proof?  }
  else
    return none

public def rewrite : SimpFun := fun e => do
  -- **TODO**: over-applied terms
  for thm in (← read).thms.getMatch e do
    if let some result ← thm.rewrite? e then
      return result
  return { expr := e }

end Lean.Meta.Sym.Simp
