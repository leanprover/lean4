/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

abbrev UsedSet := FVarIdHashSet

/--
Collect set of (let) free variables in a LCNF value.
This code exploits the LCNF property that let-variables do not occur in types.
-/
def collectExpr (s : UsedSet) (e : Expr) : UsedSet :=
  match e with
  | .proj _ _ e => collectExpr s e
  | .forallE .. => s
  | .lam _ _ b _ => collectExpr s b
  | .letE _ _ v b _ => collectExpr (collectExpr s v) b
  | .app f a => collectExpr (collectExpr s a) f
  | .mdata _ b => collectExpr s b
  | .fvar fvarId => s.insert fvarId
  | _ => s

private def _root_.Lean.Expr.collectM (e : Expr) : StateM UsedSet Unit :=
  modify fun s => collectExpr s e

private def _root_.Lean.FVarId.collectM (fvarId : FVarId) : StateM UsedSet Unit :=
  modify fun s => s.insert fvarId

partial def Code.elimDead (code : Code) : Code :=
  go code |>.run' {}
where
  goFunDecl (funDecl : FunDecl) : StateM UsedSet FunDecl := do
    return funDecl

  go (code : Code) : StateM UsedSet Code := do
    match code with
    | .let decl k =>
      let k ← go k
      if (← get).contains decl.fvarId then
        decl.type.collectM
        decl.value.collectM
        return .let decl k
      else
        return k
    | .fun decl k =>
      let k ← go k
      if (← get).contains decl.fvarId then
        return .fun (← goFunDecl decl) k
      else
        return k
    | .jp decl k =>
      let k ← go k
      if (← get).contains decl.fvarId then
        return .jp (← goFunDecl decl) k
      else
        return k
    | .cases c =>
      let alts ← c.alts.mapM fun
        | .alt ctorName params k => return .alt ctorName params (← go k)
        | .default k => return .default (← go k)
      c.discr.collectM
      return .cases { c with alts }
    | .return fvarId => fvarId.collectM; return code
    | .jmp fvarId args => fvarId.collectM; args.forM (·.collectM); return code
    | .unreach .. => return code

def Decl.elimDead (decl : Decl) : Decl :=
  { decl with value := decl.value.elimDead }

end Lean.Compiler.LCNF