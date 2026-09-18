/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Injection
import Init.Data.Nat.Internal.Linear
import Lean.Structure
import Lean.ProjFns
import Lean.Meta.Tactic.Reparametrize

public section

namespace Lean.Meta

/-- Convert heterogeneous equality into a homogeneous one -/
private def heqToEq' (mvarId : MVarId) (eqDecl : LocalDecl) : MetaM MVarId := do
  /- Convert heterogeneous equality into a homogeneous one -/
  let prf    ← mkEqOfHEq (mkFVar eqDecl.fvarId)
  let aEqb   ← whnf (← inferType prf)
  let mvarId ← mvarId.assert eqDecl.userName aEqb prf
  mvarId.clear eqDecl.fvarId

structure UnifyEqResult where
  mvarId    : MVarId
  subst     : FVarSubst
  numNewEqs : Nat := 0

private def toOffset? (e : Expr) : MetaM (Option (Expr × Nat)) := do
  match (← evalNat e) with
  | some k => return some (mkNatLit 0, k)
  | none => isOffset? e

/--
Solves the equation `eqDecl : a = b` of type `α` if it is of the form `c x = t` or `t = c x`, where
`c` is a chain of constructors and projections of one-field structures and `x` is a free variable not occurring in `t`, by the definitional change of variables `x := c⁻¹ t`: the
equation is replaced by `x = c⁻¹ t`, which `unifyEq?` substitutes in its next round.
-/
private def unifyEqInvertingBijections? (mvarId : MVarId) (eqDecl : LocalDecl) (subst : FVarSubst)
    (α a b : Expr) : MetaM (Option UnifyEqResult) := do
  let go (bx t : Expr) (symm : Bool) : MetaM (Option UnifyEqResult) := do
    let some ⟨x, bs⟩ ← OneFieldStructure.bijectionWrappedFVar? bx
      | return none
    if t.containsFVar x || (← x.getDecl).isLet then return none
    let inv (e : Expr) := bs.foldrM (·.inv.mkAppAndSimplify ·) e
    let prf := eqDecl.toExpr
    let prf ← if symm then mkEqSymm prf else pure prf
    let prf ← mkCongrArg (← withLocalDeclD `z α fun z => do mkLambdaFVars #[z] (← inv z)) prf
    let mvarId ← mvarId.assert eqDecl.userName (← mkEq (mkFVar x) (← inv t)) prf
    let mvarId ← mvarId.clear eqDecl.fvarId
    return some { mvarId, subst, numNewEqs := 1 }
  if let some r ← go a b (symm := false) then return some r
  go b a (symm := true)

/--
  Helper method for methods such as `Cases.unifyEqs?`.
  Given the given goal `mvarId` containing the local hypothesis `eqFVarId`, it performs the following operations:

  - If `eqFVarId` is a heterogeneous equality, tries to convert it to a homogeneous one.
  - If `eqFVarId` is a homogeneous equality of the form `a = b`, it tries
     - If `a` and `b` are definitionally equal, clear it
     - Normalize `a` and `b` using the current reducibility setting.
     - If `a` (`b`) is a free variable not occurring in `b` (`a`), replace it everywhere.
     - If `a` and `b` are distinct constructors, return `none` to indicate that the goal has been closed.
     - If `a` and `b` are the same constructor, apply `injection`, the result contains the number of new equalities introduced in the goal.
     - If `a` (`b`) is a chain of constructors and projections of one-field structures applied to a free variable
       not occurring in `b` (`a`), replace the equation by one that substitutes the variable, see `changeOfVariables?`.
     - It also tries to apply the given `acyclic` method to try to close the goal.
       Remark: It is a parameter because `simp` uses `unifyEq?`, and `acyclic` depends on `simp`.
-/
def unifyEq? (mvarId : MVarId) (eqFVarId : FVarId) (subst : FVarSubst := {})
             (acyclic : MVarId → Expr → MetaM Bool := fun _ _ => return false)
             (caseName? : Option Name := none)
             : MetaM (Option UnifyEqResult) := do
   mvarId.withContext do
    let eqDecl ← eqFVarId.getDecl
    if eqDecl.type.isHEq then
      let mvarId ← heqToEq' mvarId eqDecl
      return some { mvarId, subst, numNewEqs := 1 }
    else match eqDecl.type.eq? with
      | none => throwError "Expected an equality, but found{indentExpr eqDecl.type}"
      | some (α, a, b) =>
        /-
          Remark: we do not check `isDefeq` here because we would fail to substitute equalities
          such as `x = t` and `t = x` when `x` and `t` are proofs (proof irrelevance).
        -/
        /- Remark: we use `let rec` here because otherwise the compiler would generate an insane amount of code.
          We can remove the `rec` after we fix the eagerly inlining issue in the compiler. -/
        let rec substEq (symm : Bool) := do
          /-
          Remark: `substCore` fails if the equation is of the form `x = x`
          We use `(tryToSkip := true)` to ensure we avoid unnecessary `Eq.rec`s in user code.
          Recall that `Eq.rec`s can negatively affect term reduction performance in the kernel and elaborator.
          See issue https://github.com/leanprover/lean4/issues/2552 for an example.
          -/
          if let some (subst, mvarId) ← observing? (substCore mvarId eqFVarId symm subst (tryToSkip := true)) then
            return some { mvarId, subst }
          else if (← isDefEq a b) then
            /- Skip equality -/
            return some { mvarId := (←  mvarId.clear eqFVarId), subst }
          else if (← acyclic mvarId (mkFVar eqFVarId)) then
            return none -- this alternative has been solved
          else
            throwError "Dependent elimination failed: Failed to solve equation{indentExpr eqDecl.type}"
        /- Special support for offset equalities -/
        let injectionOffset? (a b : Expr) := do
          unless (← getEnv).contains ``Nat.Internal.elimOffset do return none
          let some (xa, ka) ← toOffset? a | return none
          let some (xb, kb) ← toOffset? b | return none
          if ka == 0 || kb == 0 then return none -- use default noConfusion
          let (x, y, k) ← if ka < kb then
            pure (xa, (← mkAdd xb (mkNatLit (kb - ka))), ka)
          else if ka = kb then
            pure (xa, xb, ka)
          else
            pure ((← mkAdd xa (mkNatLit (ka - kb))), xb, kb)
          let target ← mvarId.getType
          let u ← getLevel target
          let newTarget ← mkArrow (← mkEq x y) target
          let tag ← mvarId.getTag
          let newMVar ← mkFreshExprSyntheticOpaqueMVar newTarget tag
          let val := mkAppN (mkConst ``Nat.Internal.elimOffset [u]) #[target, x, y, mkNatLit k, eqDecl.toExpr, newMVar]
          mvarId.assign val
          let mvarId ← newMVar.mvarId!.tryClear eqDecl.fvarId
          return some mvarId
        let rec injection (a b : Expr) := do
          if let some mvarId ← injectionOffset? a b then
            return some { mvarId, numNewEqs := 1, subst }
          if (← isConstructorApp a <&&> isConstructorApp b) then
            /- ctor_i ... = ctor_j ... -/
            match (← injectionCore mvarId eqFVarId) with
            | InjectionResultCore.solved                   => return none -- this alternative has been solved
            | InjectionResultCore.subgoal mvarId numNewEqs => return some { mvarId, numNewEqs, subst }
          else
            let a' ← whnf a
            let b' ← whnf b
            if a' != a || b' != b then
              /- Reduced lhs/rhs of current equality -/
              let prf := mkFVar eqFVarId
              let aEqb'  ← mkEq a' b'
              let mvarId ← mvarId.assert eqDecl.userName aEqb' prf
              let mvarId ←  mvarId.clear eqFVarId
              return some { mvarId, subst, numNewEqs := 1 }
            else if let some r ← unifyEqInvertingBijections? mvarId eqDecl subst α a b then
              return some r
            else
              match caseName? with
              | none => throwError "Dependent elimination failed: Failed to solve equation{indentExpr eqDecl.type}"
              | some caseName => throwError "Dependent elimination failed: Failed to solve equation{indentExpr eqDecl.type}\nat case `{.ofConstName caseName}`"
        let a ← instantiateMVars a
        let b ← instantiateMVars b
        match a, b with
        | Expr.fvar aFVarId, Expr.fvar bFVarId =>
          /- x = y -/
          let aDecl ← aFVarId.getDecl
          let bDecl ← bFVarId.getDecl
          substEq (aDecl.index < bDecl.index)
        | Expr.fvar .., _   => /- x = t -/ substEq (symm := false)
        | _, Expr.fvar ..   => /- t = x -/ substEq (symm := true)
        | a, b              =>
          if (← isDefEq a b) then
            /- Skip equality -/
            return some { mvarId := (← mvarId.clear eqFVarId), subst }
          else
            injection a b

end Lean.Meta
