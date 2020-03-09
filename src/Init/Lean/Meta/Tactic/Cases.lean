/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.AppBuilder
import Init.Lean.Meta.Tactic.Induction
import Init.Lean.Meta.Tactic.Injection
import Init.Lean.Meta.Tactic.Assert
import Init.Lean.Meta.Tactic.Subst

namespace Lean
namespace Meta

private def mkEqAndProof (lhs rhs : Expr) : MetaM (Expr × Expr) := do
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
    (newEqType, newRefl) ← mkEqAndProof index newIndex;
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
      (newEqType, newRefl) ← mkEqAndProof fvarDecl.toExpr h';
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
      (indicesFVarIds, newMVarId) ← introN newMVar.mvarId! newIndices.size [] false;
      (fvarId, newMVarId) ← intro1 newMVarId false;
      pure {
        mvarId         := newMVarId,
        indicesFVarIds := indicesFVarIds,
        fvarId         := fvarId,
        numEqs         := newEqs.size
      }
    | _ => throwTacticEx `generalizeIndices mvarId "inductive type expected"

structure CasesSubgoal extends InductionSubgoal :=
(ctorName : Name)

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
if !env.contains `Eq || !env.contains `HEq then pure none
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

private def elimAuxIndices (s₁ : GeneralizeIndicesSubgoal) (s₂ : Array InductionSubgoal) : MetaM (Array InductionSubgoal) :=
let indicesFVarIds := s₁.indicesFVarIds;
s₂.mapM $ fun s => do
  indicesFVarIds.foldlM
    (fun s indexFVarId =>
      let indexFVarId' := s.subst.get indexFVarId;
      (do mvarId ← clear s.mvarId indexFVarId'; pure { mvarId := mvarId, subst := s.subst.erase indexFVarId, .. s })
      <|>
      (pure s))
    s

private def toCasesSubgoals (s : Array InductionSubgoal) (ctorNames : Array Name) : Array CasesSubgoal :=
s.mapIdx $ fun i s => { ctorName := ctorNames.get! i, toInductionSubgoal := s }

private partial def unifyEqsAux : Nat → CasesSubgoal → MetaM (Option CasesSubgoal)
| 0,   s => do
  trace! `Meta.cases ("unifyEqs " ++ MessageData.ofGoal s.mvarId);
  pure (some s)
| n+1, s => do
  trace! `Meta.cases ("unifyEqs [" ++ toString (n+1) ++ "] " ++ MessageData.ofGoal s.mvarId);
  (eqFVarId, mvarId) ← intro1 s.mvarId;
  withMVarContext mvarId $ do
    eqDecl ← getLocalDecl eqFVarId;
    match eqDecl.type.heq? with
    | some (α, a, β, b) => do
      prf    ← mkEqOfHEq (mkFVar eqFVarId);
      aEqb   ← mkEq a b;
      mvarId ← assert mvarId eqDecl.userName aEqb prf;
      mvarId ← clear mvarId eqFVarId;
      unifyEqsAux (n+1) { mvarId := mvarId, .. s }
    | none => match eqDecl.type.eq? with
      | some (α, a, b) =>
        let skip : Unit → MetaM (Option CasesSubgoal) := fun _ => do {
          mvarId ← clear mvarId eqFVarId;
          unifyEqsAux n { mvarId := mvarId, .. s }
        };
        let substEq (symm : Bool) : MetaM (Option CasesSubgoal) := do {
          (newSubst, mvarId) ← substCore mvarId eqFVarId false true;
          unifyEqsAux n {
            mvarId := mvarId,
            subst  := newSubst.compose s.subst,
            fields := s.fields.map $ fun fvarId => newSubst.get fvarId,
            .. s
          }
        };
        let inj : Unit → MetaM (Option CasesSubgoal) := fun _ => do {
          r ← injectionCore mvarId eqFVarId;
          match r with
          | InjectionResultCore.solved           => pure none -- this alternative has been solved
          | InjectionResultCore.subgoal mvarId _ => unifyEqsAux n { mvarId := mvarId, .. s }
        };
        condM (isDefEq a b) (skip ()) $
        match a, b with
        | Expr.fvar aFVarId _, Expr.fvar bFVarId _ => do aDecl ← getLocalDecl aFVarId; bDecl ← getLocalDecl bFVarId; substEq (aDecl.index < bDecl.index)
        | Expr.fvar _ _,       _                   => substEq false
        | _,                   Expr.fvar _ _       => substEq true
        | _,                   _                   => inj ()
      | none => throwTacticEx `cases mvarId "equality expected"

private def unifyEqs (numEqs : Nat) (subgoals : Array CasesSubgoal) : MetaM (Array CasesSubgoal) :=
subgoals.foldlM
  (fun subgoals s => do
    s? ← unifyEqsAux numEqs s;
    match s? with
    | none   => pure $ subgoals
    | some s => pure $ subgoals.push s)
  #[]

def cases (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array (List Name) := #[]) (useUnusedNames := false) : MetaM (Array CasesSubgoal) :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `cases;
  context? ← mkCasesContext? majorFVarId;
  match context? with
  | none     => throwTacticEx `cases mvarId "not applicable to the given hypothesis"
  | some ctx =>
    let ctors := ctx.inductiveVal.ctors.toArray;
    let casesOn := mkCasesOnFor ctx.inductiveVal.name;
    condM (hasIndepIndices ctx)
      (do
        s ← induction mvarId majorFVarId casesOn givenNames useUnusedNames;
        pure $ toCasesSubgoals s ctors)
      (do
        s₁ ← generalizeIndices mvarId majorFVarId;
        trace! `Meta.cases ("after generalizeIndices" ++ Format.line ++ MessageData.ofGoal s₁.mvarId);
        s₂ ← induction s₁.mvarId s₁.fvarId casesOn givenNames useUnusedNames;
        s₂ ← elimAuxIndices s₁ s₂;
        let s₂ := toCasesSubgoals s₂ ctors;
        unifyEqs s₁.numEqs s₂)

end Cases

def cases (mvarId : MVarId) (majorFVarId : FVarId) (givenNames : Array (List Name) := #[]) (useUnusedNames := false) : MetaM (Array CasesSubgoal) :=
Cases.cases mvarId majorFVarId givenNames useUnusedNames

end Meta
end Lean
