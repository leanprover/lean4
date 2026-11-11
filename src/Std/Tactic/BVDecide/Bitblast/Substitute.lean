/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Init.System.ST
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr
public import Std.Data.HashMap.Basic

/-!
This module provides univerified substitution of atoms reflected bitvec expressions.
In addition, the substitution performs constant folding as it builds up the new expression tree.
-/

namespace Std.Tactic.BVDecide

/--
`α` is a substitution for BitVec atoms.
-/
public class AtomSubstitution (α : Type) where
  /--
  `bvAtom subst w idx` returns the expression we want to substitute the atom `idx` with or `none`.
  -/
  bvAtom : α → (w : Nat) → Nat → Option (BVExpr w)
  /--
  `boolAtom subst idx` returns the expression we want to substitute the atom `idx` with or `none`.
  -/
  boolAtom : α → Nat → Option BVLogicalExpr := fun _ _ => none

namespace Substitute

structure Cache where
  exprMap : Std.DHashMap BVExpr.Cache.Key (fun k => BVExpr k.w) := {}
  logicalMap : Std.HashMap BVLogicalExpr BVLogicalExpr := {}

abbrev SubstM (α σ : Type) := ReaderT α StateRefT Cache (ST σ)

@[inline]
def SubstM.run (subst : α) (x : (σ : Type) → SubstM α σ β) : β :=
  runST fun σ =>
    let x : SubstM α σ β := x σ
    StateRefT'.run' (ReaderT.run x subst) {}

variable {α : Type} [AtomSubstitution α]

partial def BVExpr.substM (expr : BVExpr w) : SubstM α σ (BVExpr w) := do
  let key := ⟨w, expr⟩
  if let some res := (← get).exprMap.get? key then
    return res
  else
    let res ← go expr
    modify fun s => { s with exprMap := s.exprMap.insert key res }
    return res
where
  go {w : Nat} (expr : BVExpr w) : SubstM α σ (BVExpr w) :=
    match expr with
    | .var idx => do
      match AtomSubstitution.bvAtom (← read) w idx with
      | some replacement => substM replacement
      | none => return .var idx
    | .const val => return .const val
    | .extract start len expr => do
      match ← substM expr with
      | .const val => return .const (BitVec.extractLsb' start len val)
      | expr => return .extract start len expr
    | .bin lhs op rhs => do
      match ← substM lhs, ← substM rhs with
      | .const lhs, .const rhs => return .const (op.eval lhs rhs)
      | lhs, rhs => return .bin lhs op rhs
    | .un op operand => do
      match ← substM operand with
      | .const val => return .const (op.eval val)
      | operand => return .un op operand
    | .append lhs rhs h => do
      match ← substM lhs, ← substM rhs with
      | .const lhs, .const rhs => return .const (h ▸ (lhs ++ rhs))
      | lhs, rhs => return .append lhs rhs h
    | .replicate n expr h => do
      match ← substM expr with
      | .const val => return .const (h ▸ BitVec.replicate n val)
      | expr => return .replicate n expr h
    | .shiftLeft lhs rhs => do
      match ← substM lhs, ← substM rhs with
      | .const lhs, .const rhs => return .const (lhs <<< rhs)
      | lhs, rhs => return .shiftLeft lhs rhs
    | .shiftRight lhs rhs => do
      match ← substM lhs, ← substM rhs with
      | .const lhs, .const rhs => return .const (lhs >>> rhs)
      | lhs, rhs => return .shiftRight lhs rhs
    | .arithShiftRight lhs rhs => do
      match ← substM lhs, ← substM rhs with
      | .const lhs, .const rhs => return .const (BitVec.sshiftRight' lhs rhs)
      | lhs, rhs => return .arithShiftRight lhs rhs

def BVPred.substM (pred : BVPred) : SubstM α σ BVLogicalExpr := do
  match pred with
  | .bin lhs op rhs =>
    match ← BVExpr.substM lhs, ← BVExpr.substM rhs with
    | .const lhs, .const rhs => return .const (op.eval lhs rhs)
    | lhs, rhs => return .literal (.bin lhs op rhs)
  | .getLsbD expr idx =>
    match ← BVExpr.substM expr with
    | .const val => return .const (val.getLsbD idx)
    | expr => return .literal (.getLsbD expr idx)

def mkNot : BVLogicalExpr → BVLogicalExpr
  | .const b => .const !b
  | .not x => x
  | x => .not x

def mkGate (g : Gate) (x y : BVLogicalExpr) : BVLogicalExpr :=
  match g, x, y with
  | g, .const x, .const y => .const (g.eval x y)
  | .and, .const false, _ | .and, _, .const false => .const false
  | .and, .const true, z | .and, z, .const true => z
  | .or, .const true, _ | .or, _, .const true => .const true
  | .or, .const false, z | .or, z, .const false => z
  | .xor, .const b, z | .xor, z, .const b => if b then mkNot z else z
  | .beq, .const b, z | .beq, z, .const b => if b then z else mkNot z
  | g, x, y => .gate g x y

partial def BVLogicalExpr.substM (expr : BVLogicalExpr) : SubstM α σ BVLogicalExpr := do
  if let some res := (← get).logicalMap[expr]? then
    return res
  else
    let res ← go expr
    modify fun s => { s with logicalMap := s.logicalMap.insert expr res }
    return res
where
  go (expr : BVLogicalExpr) : SubstM α σ BVLogicalExpr :=
    match expr with
    | .literal pred@(.getLsbD (w := 1) (.var idx) 0) => do
      match AtomSubstitution.boolAtom (← read) idx with
      | some replacement => substM replacement
      | none => BVPred.substM pred
    | .literal pred => BVPred.substM pred
    | .const b => return .const b
    | .not x => return mkNot (← substM x)
    | .gate g x y => return mkGate g (← substM x) (← substM y)
    | .ite d l r => do
      match ← substM d with
      | .const true => substM l
      | .const false => substM r
      | d => return .ite d (← substM l) (← substM r)

end Substitute

open Substitute

public def BVExpr.substitute [AtomSubstitution α] (subst : α) (expr : BVExpr w) : BVExpr w :=
  SubstM.run subst fun σ => BVExpr.substM (σ := σ) expr

public def BVLogicalExpr.substitute [AtomSubstitution α] (subst : α) (expr : BVLogicalExpr) :
    BVLogicalExpr :=
  SubstM.run subst fun σ => BVLogicalExpr.substM (σ := σ) expr

public def BVLogicalExpr.substituteAll [AtomSubstitution α] (subst : α)
    (exprs : Array BVLogicalExpr) : Array BVLogicalExpr :=
  SubstM.run subst fun σ => exprs.mapM (BVLogicalExpr.substM (σ := σ))

end Std.Tactic.BVDecide
