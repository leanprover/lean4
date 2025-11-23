/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski, Joachim Breitner
-/

module

prelude
public import Lean.Meta.PProdN
public import Lean.Meta.AppBuilder
public import Init.Internal.Order.Basic

public section

/-!
This module has meta-functions for constructions expressions related to `Lean.Order`.
In particular some of these functions can handle the `CCPO` and `CompleteLattice`
structures conveniently uniformly, picking the right one based on the type of the arguments.
-/

namespace Lean.Meta
open Order

/--
Given `inst : CCPO (t[x])` for some FVar `x`, constructs an instance
of the type `CCPO (∀ x, t[x])`.
Can handle `CompleteLattice` as well.
--/
def mkInstPiOfInstForall (x : Expr) (inst : Expr) : MetaM Expr := do
  if (←inferType inst).isAppOf ``CCPO then
    mkAppOptM ``instCCPOPi #[(← inferType x), none, (← mkLambdaFVars #[x] inst)]
  else if (←inferType inst).isAppOf ``CompleteLattice then
    mkAppOptM ``instCompleteLatticePi #[(← inferType x), none, (← mkLambdaFVars #[x] inst)]
  else
    throwError "mkInstPiOfInstForall: unexpected type of {inst}"

/-- An n-ary version of `mkInstPiOfInstForall`. Takes an array of arguments instead.
--/
def mkInstPiOfInstsForall (xs : Array Expr) (inst : Expr) : MetaM Expr := do
  let mut inst := inst
  for x in xs.reverse do
    inst ← mkInstPiOfInstForall x inst
  pure inst

/--
Given a function `f : α → α`, an instance `inst : CCPO α`
and a monotonicity proof `hmono : monotone f`, constructs a least fixpoint of `f`
with respect to the instance `inst`. The `packedType` is assumed to contain the type `α`.
Can handle `CompleteLattice` as well.
-/
def mkFixOfMonFun (packedType : Expr) (packedInst : Expr) (hmono : Expr) : MetaM Expr := do
  if (←inferType packedInst).isAppOf ``CCPO then
    mkAppOptM ``fix #[packedType, packedInst, none, hmono]
  else if (←inferType packedInst).isAppOf ``CompleteLattice then
    mkAppOptM ``lfp_monotone #[packedType, packedInst, none, hmono]
  else
    throwError "mkFixOfMonFun: unexpected type of {packedInst}"

/--
Given `packedInst : CCPO α `, returns an underlying instance of the type
`PartialOrder α`. Can handle `CompleteLattice` as well.
Takes an optional argument with the type `α`. If the optional argument is `none`,
it is treated implicitly.
-/
def toPartialOrder (packedInst : Expr) (type : Option Expr := .none) := do
  if (←inferType packedInst).isAppOf ``CCPO then
    mkAppOptM ``CCPO.toPartialOrder #[type, packedInst]
  else if (←inferType packedInst).isAppOf ``CompleteLattice then
    mkAppOptM ``CompleteLattice.toPartialOrder #[type, packedInst]
  else
    throwError "getUnderlyingOrder: unexpected type of {packedInst}"

/--
Given CCPO instances `inst₁ : CCPO α₁` and `inst₂ : CCPO α₂`,
constructs an instance of the type `CCPO (α₁ × α₂)`.
-/
def mkInstCCPOPProd (inst₁ inst₂ : Expr) : MetaM Expr := do
  mkAppOptM ``instCCPOPProd #[none, none, inst₁, inst₂]

/--
Given CCPO instances `inst₁ : CompleteLattice α₁` and `inst₂ : CompleteLattice α₂`,
constructs an instance of the type `CompleteLattice (α₁ × α₂)`.
-/
def mkInstCompleteLatticePProd (inst₁ inst₂ : Expr) : MetaM Expr := do
  mkAppOptM ``instCompleteLatticePProd #[none, none, inst₁, inst₂]

/--
Given an array of CCPO instances `insts = #[CCPO α₁, ..., CCPO αₙ]`, constructs an instance
of the type `CCPO (α₁ × ... × αₙ)`.
Can handle `CompleteLattice` as well.
-/
def mkPackedPPRodInstance (insts : Array Expr) : MetaM Expr := do
  let types ← insts.mapM inferType
  if (types.all (fun t => t.isAppOf ``CCPO)) then
    PProdN.genMk mkInstCCPOPProd insts
  else if (types.all (fun t => t.isAppOf ``CompleteLattice)) then
    PProdN.genMk mkInstCompleteLatticePProd insts
  else
    throwError "mkPackedPPRoodInstance: unexpected types {types} of {insts}"
