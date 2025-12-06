/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
public section
namespace Lean.Meta.Simp.Arith

private def isSupportedType (type : Expr) : Bool :=
  match_expr type with
  | Nat => true
  | Int => true
  | _ => false

private def isSupportedCommRingType (type : Expr) : Bool :=
  match_expr type with
  | Int => true
  | _ => false

/-- Quick filter for linear terms. -/
def isLinearTerm? (e : Expr) : Option Expr :=
  match_expr e with
  | HAdd.hAdd α _ _ _ _ _ => .guard isSupportedType α
  | HMul.hMul α _ _ _ _ _ => .guard isSupportedType α
  | HSub.hSub α _ _ _ _ _ => .guard isSupportedCommRingType α
  | Neg.neg α _ _ => .guard isSupportedCommRingType α
  | Nat.succ _ => some Nat.mkType
  | _ => none

def isLinearTerm (e : Expr) : Bool :=
  isLinearTerm? e |>.isSome

def isLinearPosCnstr (e : Expr) : Bool :=
  match_expr e with
  | Eq α _ _ => isSupportedType α
  | Ne α _ _ => isSupportedType α
  | LE.le α _ _ _ => isSupportedType α
  | LT.lt α _ _ _ => isSupportedType α
  | GT.gt α _ _ _ => isSupportedType α
  | GE.ge α _ _ _ => isSupportedType α
  | _ => false

def isLinearCnstr (e : Expr) : Bool :=
  match_expr e with
  | Not p => isLinearPosCnstr p
  | _ => isLinearPosCnstr e

def isDvdCnstr (e : Expr) : Bool :=
  match_expr e with
  | Dvd.dvd α _ _ _ => isSupportedType α
  | _ => false

end Lean.Meta.Simp.Arith
