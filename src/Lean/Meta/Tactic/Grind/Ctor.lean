/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Injective
import Lean.Meta.Tactic.Grind.Simp
public section
namespace Lean.Meta.Grind

private partial def propagateInjEqs (eqs : Expr) (proof : Expr) (generation : Nat) : GoalM Unit := do
  -- Remark: we must use `shareCommon` before using `pushEq` and `pushHEq`.
  -- This is needed because the result type of the injection theorem may allocate
  match_expr eqs with
  | And left right =>
    propagateInjEqs left (.proj ``And 0 proof) generation
    propagateInjEqs right (.proj ``And 1 proof) generation
  | Eq _ lhs rhs    =>
    let lhs ← preprocessLight lhs
    let rhs ← preprocessLight rhs
    internalize lhs generation
    internalize rhs generation
    pushEq lhs rhs proof
  | HEq _ lhs _ rhs =>
    let lhs ← preprocessLight lhs
    let rhs ← preprocessLight rhs
    internalize lhs generation
    internalize rhs generation
    pushHEq lhs rhs proof
  | _ =>
   reportIssue! "unexpected injectivity theorem result type{indentExpr eqs}"
   return ()

/-- Homogeneous case where constructor applications `a` and `b` have the same type `α`. -/
private def propagateCtorHomo (α : Expr) (a b : Expr) : GoalM Unit := do
  let ctor₁ := a.getAppFn
  let ctor₂ := b.getAppFn
  if ctor₁ == ctor₂ then
    let .const ctorName _ := ctor₁ | return ()
    let injDeclName := mkInjectiveTheoremNameFor ctorName
    unless (← getEnv).contains injDeclName do return ()
    let info ← getConstInfo injDeclName
    let n := info.type.getForallArity
    let mask : Array (Option Expr) := .replicate n none
    /-
    We use `mkExpectedTypeHint` here to ensure that `mkAppOptM` will "fill" the implicit
    arguments of `injDeclName` using exactly the fields of `a` and `b`.
    There is no guarantee that `inferType (← mkEqProof a b)` is structurally equal to `a = b`.
    -/
    let mask := mask.set! (n-1) (some (← mkExpectedTypeHint (← mkEqProof a b) (← mkEq a b)))
    let injLemma ← mkAppOptM injDeclName mask
    let injLemmaType ← inferType injLemma
    let gen := max (← getGeneration a) (← getGeneration b)
    propagateInjEqs injLemmaType injLemma gen
  else
    let .const declName _ := α.getAppFn | return ()
    let noConfusionDeclName := Name.mkStr declName "noConfusion"
    unless (← getEnv).contains noConfusionDeclName do return ()
    closeGoal (← mkNoConfusion (← getFalseExpr) (← mkEqProof a b))

/-- Heterogeneous case where constructor applications `a` and `b` have different types `α` and `β`. -/
private def propagateCtorHetero (a b : Expr) : GoalM Unit := do
  a.withApp fun ctor₁ args₁ =>
  b.withApp fun ctor₂ args₂ => do
  let .const ctorName₁ us₁ := ctor₁ | return ()
  let .const ctorName₂ us₂ := ctor₂ | return ()
  let .ctorInfo ctorVal₁ ← getConstInfo ctorName₁ | return ()
  let .ctorInfo ctorVal₂ ← getConstInfo ctorName₂ | return ()
  unless ctorVal₁.induct == ctorVal₂.induct do return ()
  let params₁ := args₁[*...ctorVal₁.numParams]
  let params₂ := args₂[*...ctorVal₂.numParams]
  if  params₁.size ≠ params₂.size then return () else
  unless us₁.length == us₂.length do return ()
  unless (← us₁.zip us₂ |>.allM fun (u₁, u₂) => isLevelDefEq u₁ u₂) do return ()
  let gen := max (← getGeneration a) (← getGeneration b)
  if ctorName₁ == ctorName₂ then
    let hinjDeclName := mkHInjectiveTheoremNameFor ctorName₁
    unless (← getEnv).containsOnBranch hinjDeclName do
      let _ ← executeReservedNameAction hinjDeclName
    let proof := mkConst hinjDeclName us₁
    let proof := mkAppN (mkAppN proof args₁) args₂
    addNewRawFact proof (← inferType proof) gen (.inj (.decl hinjDeclName))
  else
    let some indices₁ ← getCtorAppIndices? a | return ()
    let some indices₂ ← getCtorAppIndices? b | return ()
    let noConfusionName := ctorVal₁.induct.str "noConfusion"
    let noConfusion := mkConst noConfusionName (0 :: us₁)
    let noConfusion := mkApp noConfusion (← getFalseExpr)
    let noConfusion := mkApp (mkAppN noConfusion (params₁ ++ indices₁)) a
    let noConfusion := mkApp (mkAppN noConfusion (params₂ ++ indices₂)) b
    let proof := noConfusion
    addNewRawFact proof (← inferType proof) gen (.inj (.decl noConfusionName))

/--
Given constructors `a` and `b`, propagate equalities if they are the same,
and close goal if they are different.
-/
def propagateCtor (a b : Expr) : GoalM Unit := do
  let aType ← whnfD (← inferType a)
  let bType ← whnfD (← inferType b)
  if (← isDefEqD aType bType) then
    propagateCtorHomo aType a b
  else
    propagateCtorHetero a b

end Lean.Meta.Grind
