/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Tactic.Induction

namespace Lean
namespace Meta

private def mkEq (lhs rhs : Expr) : MetaM (Expr × Expr) := do
lhsType ← inferType lhs;
rhsType ← inferType rhs;
u       ← getLevel lhsType;
condM (isDefEq lhsType rhsType)
  (pure (mkApp3 (mkConst `Eq [u]) lhsType lhs rhs, mkApp2 (mkConst `Eq.refl [u]) lhsType lhs))
  (pure (mkApp4 (mkConst `HEq [u]) lhsType lhs rhsType rhs, mkApp2 (mkConst `HEq.refl [u]) lhsType lhs))

private partial def withNewIndexEqsAux {α} (indices newIndices : Array Expr) (k : Array Expr → Array Expr → MetaM α) : Nat → Array Expr → Array Expr → MetaM α
| i, newEqs, newRefls =>
  if h : i < indices.size then do
    let index    := indices.get! i;
    let newIndex := newIndices.get! i;
    (newEqType, newRefl) ← mkEq index newIndex;
    withLocalDecl `h newEqType BinderInfo.default $ fun newEq => do
    withNewIndexEqsAux (i+1) (newEqs.push newEq) (newRefls.push newRefl)
  else
    k newEqs newRefls

private def withNewIndexEqs {α} (indices newIndices : Array Expr) (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
withNewIndexEqsAux indices newIndices k 0 #[] #[]

structure GeneralizeIndicesSubgoal :=
(mvarId         : MVarId)
(indicesFVarIds : Array FVarId)
(fvarId         : FVarId)
(numEqs         : Nat)

/--
  Given a metavariable `mvarId` representing the
  ```
  Ctx, h : I A j, D |- T
  ```
  where `fvarId` is `h`s id, and the type `I A j` is an inductive datatype where `A` are parameters,
  and `j` the indices. Generate the goal
  ```
  Ctx, h : I A j, D, j' : J, h' : I A j' |- j == j' -> h == h' -> T
  ```
  Remark: `(j == j' -> h == h')` is a "telescopic" equality.
  Remark: `j` is sequence of terms, and `j'` a sequence of free variables.
  The result contains the fields
  - `mvarId`: the new goal
  - `indicesFVarIds`: `j'` ids
  - `fvarId`: `h'` id
  - `numEqs`: number of equations in the target -/
def generalizeIndices (mvarId : MVarId) (fvarId : FVarId) : MetaM GeneralizeIndicesSubgoal := do
withMVarContext mvarId $ do
  lctx       ← getLCtx;
  localInsts ← getLocalInstances;
  env        ← getEnv;
  checkNotAssigned mvarId `generalizeIndices;
  fvarDecl ← getLocalDecl fvarId;
  type ← whnf fvarDecl.type;
  type.withApp $ fun f args => matchConst env f (fun _ => throwTacticEx `generalizeIndices mvarId "inductive type expected") $
    fun cinfo _ => match cinfo with
    | ConstantInfo.inductInfo val => do
      unless (val.nindices > 0) $ throwTacticEx `generalizeIndices mvarId "indexed inductive type expected";
      unless (args.size == val.nindices + val.nparams) $ throwTacticEx `generalizeIndices mvarId "ill-formed inductive datatype";
      let indices := args.extract (args.size - val.nindices) args.size;
      let IA := mkAppN f (args.extract 0 val.nparams); -- `I A`
      IAType ← inferType IA;
      forallTelescopeReducing IAType $ fun newIndices _ => do
      let newType := mkAppN IA newIndices;
      withLocalDecl fvarDecl.userName newType BinderInfo.default $ fun h' =>
      withNewIndexEqs indices newIndices $ fun newEqs newRefls => do
      (newEqType, newRefl) ← mkEq fvarDecl.toExpr h';
      let newRefls := newRefls.push newRefl;
      withLocalDecl `h newEqType BinderInfo.default $ fun newEq => do
      let newEqs := newEqs.push newEq;
      /- auxType `forall (j' : J) (h' : I A j'), j == j' -> h == h' -> target -/
      target  ← getMVarType mvarId;
      tag     ← getMVarTag mvarId;
      auxType ← mkForall newEqs target;
      auxType ← mkForall #[h'] auxType;
      auxType ← mkForall newIndices auxType;
      newMVar ← mkFreshExprMVarAt lctx localInsts auxType tag MetavarKind.syntheticOpaque;
      /- assign mvarId := newMVar indices h refls -/
      assignExprMVar mvarId (mkAppN (mkApp (mkAppN newMVar indices) fvarDecl.toExpr) newRefls);
      (indicesFVarIds, newMVarId) ← introN newMVar.mvarId! newIndices.size;
      (fvarId, newMVarId) ← intro1 newMVarId;
      pure {
        mvarId         := newMVarId,
        indicesFVarIds := indicesFVarIds,
        fvarId         := fvarId,
        numEqs         := newEqs.size
      }
    | _ => throwTacticEx `generalizeIndices mvarId "inductive type expected"

structure CasesSubgoal :=
(ctorName : Name)
(mvarId   : MVarId)
(fields   : Array FVarId := #[])
(subst    : FVarSubst := {})

namespace Cases

structure Context :=
(inductiveVal     : InductiveVal)
(casesOnVal       : DefinitionVal)
(nminors          : Nat := inductiveVal.ctors.length)
(majorDecl        : LocalDecl)
(majorTypeFn      : Expr)
(majorTypeArgs    : Array Expr)
(majorTypeIndices : Array Expr := majorTypeArgs.extract (majorTypeArgs.size - inductiveVal.nindices) majorTypeArgs.size)

private def mkCasesContext? (majorFVarId : FVarId) : MetaM (Option Context) := do
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
      | ConstantInfo.defnInfo cval => pure $ some {
          inductiveVal  := ival,
          casesOnVal    := cval,
          majorDecl     := majorDecl,
          majorTypeFn   := f,
          majorTypeArgs := args
        }
      | _ => pure none
    | _                           => pure none

/-
We say the major premise has independent indices IF
1- its type is *not* an indexed inductive family, OR
2- its type is an indexed inductive family, but all indices are distinct free variables, and
   all local declarations different from the major and its indices do not depend on the indices.
-/
private def hasIndepIndices (ctx : Context) : MetaM Bool :=
if ctx.majorTypeIndices.isEmpty then
  pure true
else if ctx.majorTypeIndices.any $ fun idx => !idx.isFVar then
  /- One of the indices is not a free variable. -/
  pure false
else if ctx.majorTypeIndices.size.any $ fun i => i.any $ fun j => ctx.majorTypeIndices.get! i == ctx.majorTypeIndices.get! j then
  /- An index ocurrs more than once -/
  pure false
else do
  lctx ← getLCtx;
  mctx ← getMCtx;
  pure $ lctx.all $ fun decl =>
    decl.fvarId == ctx.majorDecl.fvarId || -- decl is the major
    ctx.majorTypeIndices.any (fun index => decl.fvarId == index.fvarId!) || -- decl is one of the indices
    mctx.findLocalDeclDependsOn decl (fun fvarId => ctx.majorTypeIndices.all $ fun idx => idx.fvarId! != fvarId) -- or does not depend on any index

end Cases

def cases (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array (List Name) := #[]) (useUnusedNames := false) :
    MetaM (Array CasesSubgoal) :=
throw $ arbitrary _ -- TODO

end Meta
end Lean
