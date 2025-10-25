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
/-
To prevent the kernel from accidentally reducing the atoms in the equation while typechecking,
we abstract over them.
-/
def withAbstractAtoms (atoms : Array Expr) (type : Name) (k : Array Expr → MetaM (Option (Expr × Expr))) :
    MetaM (Option (Expr × Expr)) := do
  let type := mkConst type
  let rec go (i : Nat) (atoms' : Array Expr) (xs : Array Expr) (args : Array Expr) : MetaM (Option (Expr × Expr)) := do
    if h : i < atoms.size then
      let atom := atoms[i]
      if atom.isFVar then
        go (i+1) (atoms'.push atom) xs args
      else
        withLocalDeclD (← mkFreshUserName `x) type fun x =>
          go (i+1) (atoms'.push x) (xs.push x) (args.push atom)
    else
      if xs.isEmpty then
        k atoms'
      else
        let some (r, p) ← k atoms' | return none
        let r := (← mkLambdaFVars xs r).beta args
        let p := mkAppN (← mkLambdaFVars xs p) args
        return some (r, p)
  go 0 #[] #[] #[]

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
