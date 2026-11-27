/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Injection
import Lean.Meta.LitValues
import Lean.Meta.StringLitProof
import Init.Data.Nat.Internal.Linear
import Init.Data.Char.Basic
import Init.Data.Int.Basic
import Init.Data.SInt.Basic

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
If `a` and `b` are different literals of the same type, returns a proof of `¬ a = b`.
The literals supported are the ones of type `String`, `Nat`, `Int`, `Char`, `Fin n`, `BitVec n`,
`UInt8`, `UInt16`, `UInt32`, `UInt64`, `Int8`, `Int16`, `Int32`, and `Int64`.

For `String`, the proof is built with `mkStringLitNeProof`. For the other types, it is an
application of a theorem such as `Nat.ne_of_beq_eq_false` and `UInt8.ne_of_toNat_beq_eq_false` to
`Eq.refl false`: the kernel evaluates `Nat.beq` on two numerals, and does not unfold the
`DecidableEq` instance of the type. Only literals in their standard representation (see
`normLitValue`) are supported.
-/
private def mkLitNeProof? (a b : Expr) : MetaM (Option Expr) := do
  if let .lit (.strVal s₁) := a then
    let .lit (.strVal s₂) := b | return none
    if s₁ == s₂ then return none
    -- The theorem used in the proof is not available in the modules that precede its declaration.
    unless (← getEnv).contains ``String.Internal.ne_of_sameByteAt do return none
    return some (← mkStringLitNeProof s₁ s₂)
  -- A literal elaborated with a nonstandard instance, such as `(5 : UInt8)` with a local
  -- `OfNat UInt8 5`, may denote a different value: `neThm?` does not inspect the instance.
  unless (← normLitValue a) == a && (← normLitValue b) == b do return none
  let some thm ← neThm? | return none
  unless (← getEnv).contains thm do return none
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``false)
  -- The theorems for `Fin n` and `BitVec n` have `n` as their first argument.
  let type ← whnfR (← inferType a)
  let thm := if type.isApp then mkApp (mkConst thm) type.appArg! else mkConst thm
  return some (mkApp3 thm a b h)
where
  /-- The theorem that proves `a ≠ b`, if `a` and `b` are different literals of a supported type. -/
  neThm? : MetaM (Option Name) := do
    if let some x ← getNatValue? a then
      let some y ← getNatValue? b | return none
      return if x == y then none else some ``Nat.ne_of_beq_eq_false
    if let some x ← getIntValue? a then
      let some y ← getIntValue? b | return none
      if x == y then return none
      return if x.toNat != y.toNat then some ``Int.ne_of_toNat_beq_eq_false
        else some ``Int.ne_of_neg_toNat_beq_eq_false
    if let some x ← getCharValue? a then
      let some y ← getCharValue? b | return none
      return if x == y then none else some ``Char.ne_of_toNat_beq_eq_false
    if let some ⟨n, x⟩ ← getFinValue? a then
      let some ⟨m, y⟩ ← getFinValue? b | return none
      return if n != m || x.val == y.val then none else some ``Fin.ne_of_val_beq_eq_false
    if let some ⟨n, x⟩ ← getBitVecValue? a then
      let some ⟨m, y⟩ ← getBitVecValue? b | return none
      return if n != m || x.toNat == y.toNat then none else some ``BitVec.ne_of_toNat_beq_eq_false
    if let some x ← getUInt8Value? a then
      let some y ← getUInt8Value? b | return none
      return if x == y then none else some ``UInt8.ne_of_toNat_beq_eq_false
    if let some x ← getUInt16Value? a then
      let some y ← getUInt16Value? b | return none
      return if x == y then none else some ``UInt16.ne_of_toNat_beq_eq_false
    if let some x ← getUInt32Value? a then
      let some y ← getUInt32Value? b | return none
      return if x == y then none else some ``UInt32.ne_of_toNat_beq_eq_false
    if let some x ← getUInt64Value? a then
      let some y ← getUInt64Value? b | return none
      return if x == y then none else some ``UInt64.ne_of_toNat_beq_eq_false
    if let some x ← getInt8Value? a then
      let some y ← getInt8Value? b | return none
      return if x == y then none else some ``Int8.ne_of_toNat_beq_eq_false
    if let some x ← getInt16Value? a then
      let some y ← getInt16Value? b | return none
      return if x == y then none else some ``Int16.ne_of_toNat_beq_eq_false
    if let some x ← getInt32Value? a then
      let some y ← getInt32Value? b | return none
      return if x == y then none else some ``Int32.ne_of_toNat_beq_eq_false
    if let some x ← getInt64Value? a then
      let some y ← getInt64Value? b | return none
      return if x == y then none else some ``Int64.ne_of_toNat_beq_eq_false
    return none

/--
  Helper method for methods such as `Cases.unifyEqs?`.
  Given the given goal `mvarId` containing the local hypothesis `eqFVarId`, it performs the following operations:

  - If `eqFVarId` is a heterogeneous equality, tries to convert it to a homogeneous one.
  - If `eqFVarId` is a homogeneous equality of the form `a = b`, it tries
     - If `a` and `b` are definitionally equal, clear it
     - Normalize `a` and `b` using the current reducibility setting.
     - If `a` (`b`) is a free variable not occurring in `b` (`a`), replace it everywhere.
     - If `a` and `b` are distinct constructors, return `none` to indicate that the goal has been closed.
     - If `a` and `b` are distinct literals, return `none` to indicate that the goal has been closed.
       See `mkLitNeProof?`.
     - If `a` is `x + k`, where `k` is a positive numeral, and `b` is `0`, or vice versa, return `none`
       to indicate that the goal has been closed.
     - If `a` and `b` are the same constructor, apply `injection`, the result contains the number of new equalities introduced in the goal.
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
      | some (_, a, b) =>
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
        /- Returns `none` if `a = b` is not an offset equality, and `some r` otherwise, where `r` is
           the result of `unifyEq?`. -/
        let injectionOffset? (a b : Expr) : MetaM (Option (Option UnifyEqResult)) := do
          unless (← getEnv).contains ``Nat.Internal.elimOffset do return none
          let some (xa, ka) ← toOffset? a | return none
          let some (xb, kb) ← toOffset? b | return none
          if ka == 0 || kb == 0 then
            /- `x + k = 0` or `0 = x + k`, where `k` is positive: the goal is closed.
               `x + k` is definitionally equal to `Nat.succ (x + (k - 1))`. -/
            unless (← getEnv).contains ``Nat.succ_ne_zero && (← getEnv).contains ``Ne.symm do return none
            let hne ←
              if ka > 0 && (← evalNat b) == some 0 then
                pure (mkApp (mkConst ``Nat.succ_ne_zero) (← mkAdd xa (mkNatLit (ka - 1))))
              else if kb > 0 && (← evalNat a) == some 0 then
                mkAppM ``Ne.symm #[mkApp (mkConst ``Nat.succ_ne_zero) (← mkAdd xb (mkNatLit (kb - 1)))]
              else
                return none -- use default noConfusion
            mvarId.assign (← mkAbsurd (← mvarId.getType) (mkFVar eqFVarId) hne)
            return some none
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
          return some (some { mvarId, numNewEqs := 1, subst })
        let rec injection (a b : Expr) := do
          if let some hne ← mkLitNeProof? a b then
            mvarId.assign (← mkAbsurd (← mvarId.getType) (mkFVar eqFVarId) hne)
            return none -- this alternative has been solved
          if let some r ← injectionOffset? a b then
            return r
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
