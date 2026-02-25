/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.LitValues

/-!
# Cbv Utility Functions

Predicates for recognizing ground literal values (`isVal`, `isBuiltinValue`) and
proof terms (`isProofTerm`) in the `SymM` monad. Both are used by `cbvPre` to
short-circuit before structural dispatch.
-/

namespace Lean.Meta.Tactic.Cbv

open Lean.Meta.Sym.Simp

public def mkAppNS (f : Expr) (args : Array Expr) : Sym.SymM Expr := do
  args.foldlM Sym.Internal.mkAppS f

abbrev isNatValue (e : Expr) : Bool := (Sym.getNatValue? e).isSome
abbrev isStringValue (e : Expr) : Bool := (Sym.getStringValue? e).isSome
abbrev isIntValue (e : Expr) : Bool := (Sym.getIntValue? e).isSome
abbrev isBitVecValue (e : Expr) : Bool := (Sym.getBitVecValue? e).isSome
abbrev isFinValue (e : Expr) : Bool := (Sym.getFinValue? e).isSome
abbrev isCharValue (e : Expr) : Bool := (Sym.getCharValue? e).isSome
abbrev isRatValue (e : Expr) : Bool := (Sym.getRatValue? e).isSome
abbrev isUInt8Value (e : Expr) : Bool := (Sym.getUInt8Value? e).isSome
abbrev isUInt16Value (e : Expr) : Bool := (Sym.getUInt16Value? e).isSome
abbrev isUInt32Value (e : Expr) : Bool := (Sym.getUInt32Value? e).isSome
abbrev isUInt64Value (e : Expr) : Bool := (Sym.getUInt64Value? e).isSome
abbrev isInt8Value (e : Expr) : Bool := (Sym.getInt8Value? e).isSome
abbrev isInt16Value (e : Expr) : Bool := (Sym.getInt16Value? e).isSome
abbrev isInt32Value (e : Expr) : Bool := (Sym.getInt32Value? e).isSome
abbrev isInt64Value (e : Expr) : Bool := (Sym.getInt64Value? e).isSome

public def isVal (e : Expr) : Bool :=
  [
    isNatValue,
    isStringValue,
    isIntValue,
    isBitVecValue,
    isFinValue,
    isCharValue,
    isUInt8Value,
    isUInt16Value,
    isUInt32Value,
    isUInt64Value,
    isInt8Value,
    isInt16Value,
    isInt32Value,
    isInt64Value
  ].any (· e)

/-- Returns `.rfl (done := true)` for ground literal values of any recognized builtin type,
preventing the simplifier from recursing into them. For example, this stops the evaluator
from trying to unfold `OfNat.ofNat 2` further. -/
public def isBuiltinValue : Simproc := fun e => return .rfl (isVal e)

public def guardSimproc (p : Expr → Bool) (s : Simproc) : Simproc := fun e => do
  if p e then s e else return .rfl

/-- TODO: Handle code duplication -/
def isAlwaysZero : Level → Bool
  | .zero ..    => true
  | .mvar ..    => false
  | .param ..   => false
  | .succ ..    => false
  | .max u v    => isAlwaysZero u && isAlwaysZero v
  | .imax _ u   => isAlwaysZero u

/- Modified for the `SymM` usage -/
def isProp (e : Expr) : Sym.SymM Bool := do
  match (← isPropQuick e) with
  | .true  => return true
  | .false => return false
  | .undef =>
    let type ← Sym.inferType e
    let type ← whnfD type
    match type with
    | Expr.sort u => return isAlwaysZero (← instantiateLevelMVars u)
    | _           => return false

/- Modified for the `SymM` usage -/
def isProof (e : Expr) : Sym.SymM Bool := do
  match (← isProofQuick e) with
  | .true  => return true
  | .false => return false
  | .undef => isProp (← Sym.inferType e)

/-- Marks proof terms as done so the simplifier does not recurse into them. -/
public def isProofTerm : Simproc := fun e => do
  return .rfl (← isProof e)

end Lean.Meta.Tactic.Cbv
