/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Tactic.Induction

namespace Lean
namespace Meta

structure CasesSubgoal :=
(ctorName : Name)
(mvarId   : MVarId)
(fields   : Array FVarId := #[])
(subst    : FVarSubst := {})

namespace Cases

structure Context :=
(inductiveVal : InductiveVal)
(casesOnVal   : DefinitionVal)
(nminors      : Nat := inductiveVal.ctors.length)

private def mkCasesContex? (majorFVarId : FVarId) : MetaM (Option Context) := do
env ← getEnv;
if !env.contains `Eq || env.contains `HEq then pure none
else do
  majorDecl ← getLocalDecl majorFVarId;
  majorType ← whnf majorDecl.type;
  majorType.withApp $ fun f args => matchConst env f (fun _ => pure none) $ fun cinfo _ => do
    match cinfo with
    | ConstantInfo.inductInfo ival =>
      if args.size != ival.nindices + ival.nparams then pure none
      else match env.find? (mkNameStr ival.name "casesOn") with
      | ConstantInfo.defnInfo cval => pure $ some { inductiveVal := ival, casesOnVal := cval }
      | _ => pure none
    | _                           => pure none

private def mkEq (lhs rhs : Expr) : MetaM (Expr × Expr) := do
lhsType ← inferType lhs;
rhsType ← inferType rhs;
u       ← getLevel lhsType;
condM (isDefEq lhsType rhsType)
  (pure (mkApp3 (mkConst `Eq [u]) lhsType lhs rhs, mkApp2 (mkConst `Eq.refl [u]) lhsType lhs))
  (pure (mkApp4 (mkConst `HEq [u]) lhsType lhs rhsType rhs, mkApp2 (mkConst `HEq.refl [u]) lhsType lhs))

end Cases

def cases (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array (List Name) := #[]) (useUnusedNames := false) :
    MetaM (Array CasesSubgoal) :=
throw $ arbitrary _ -- TODO

end Meta
end Lean
