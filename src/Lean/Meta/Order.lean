/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

prelude
import Lean.Meta.InferType
import Lean.Meta.PProdN
import Lean.Meta.AppBuilder
import Init.Internal.Order.Basic

namespace Lean.Meta
open Order

def mkInstPiOfInstForall (x : Expr) (inst : Expr) : MetaM Expr := do
  if (←inferType inst).isAppOf ``CCPO then
    mkAppOptM ``instCCPOPi #[(← inferType x), none, (← mkLambdaFVars #[x] inst)]
  else if (←inferType inst).isAppOf ``CompleteLattice then
    mkAppOptM ``instCompleteLatticePi #[(← inferType x), none, (← mkLambdaFVars #[x] inst)]
  else
    throwError "mkInstPiOfInstForall: unexpected type of {inst}"

def mkFixOfMonFun (packedType : Expr) (packedInst : Expr) (hmono : Expr) : MetaM Expr := do
  if (←inferType packedInst).isAppOf ``CCPO then
    mkAppOptM ``fix #[packedType, packedInst, none, hmono]
  else if (←inferType packedInst).isAppOf ``CompleteLattice then
    mkAppOptM ``lfp_monotone #[packedType, packedInst, none, hmono]
  else
    throwError "mkFixOfMonFun: unexpected type of {packedInst}"

def toPartialOrder (packedInst : Expr) (type : Option Expr := .none) := do
  if (←inferType packedInst).isAppOf ``CCPO then
    mkAppOptM ``CCPO.toPartialOrder #[type, packedInst]
  else if (←inferType packedInst).isAppOf ``CompleteLattice then
    mkAppOptM ``CompleteLattice.toPartialOrder #[type, packedInst]
  else
    throwError "getUnderlyingOrder: unexpected type of {packedInst}"

def mkInstCCPOPProd (inst₁ inst₂ : Expr) : MetaM Expr := do
  mkAppOptM ``instCCPOPProd #[none, none, inst₁, inst₂]

def mkInstCompleteLatticePProd (inst₁ inst₂ : Expr) : MetaM Expr := do
  mkAppOptM ``instCompleteLatticePProd #[none, none, inst₁, inst₂]

def mkPackedPPRodInstance (insts : Array Expr) : MetaM Expr := do
  let types ← insts.mapM inferType
  if (types.all (fun t => t.isAppOf ``CCPO)) then
    PProdN.genMk mkInstCCPOPProd insts
  else if (types.all (fun t => t.isAppOf ``CompleteLattice)) then
    PProdN.genMk mkInstCompleteLatticePProd insts
  else
    throwError "mkPackedPPRoodInstance: unexpected types {types} of {insts}"
