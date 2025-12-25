/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.ReplaceS
import Lean.Meta.Sym.LooseBVarsS
import Init.Grind
public section
namespace Lean.Meta.Sym

/--
Similar to `Lean.Expr.instantiateRevRange`.
It assumes the input is maximally shared, and ensures the output is too.
It assumes `beginIdx ≤ endIdx` and `endIdx ≤ subst.size`
-/
def instantiateRevRangeS (e : Expr) (beginIdx endIdx : Nat) (subst : Array Expr) : SymM Expr :=
  if _ : beginIdx > endIdx then unreachable! else
  if _ : endIdx > subst.size then unreachable! else
  let s := beginIdx
  let n := endIdx - beginIdx
  replaceS e fun e offset => do
    let s₁ := s + offset
    match e with
    | .bvar idx =>
      if _h : idx >= s₁ then
        if _h : idx < offset + n then
          let v := subst[n - (idx - offset) - 1]
          liftLooseBVarsS' v 0 offset
        else
          Grind.mkBVarS (idx - n)
      else
        return some e
    | .lit _ | .mvar _ | .fvar _ | .const _ _ | .sort _ =>
      return some e
    | _ =>
      if s₁ >= e.looseBVarRange then
        return some e
      else
        return none

/--
Similar to `Lean.Expr.instantiateRev`.
It assumes the input is maximally shared, and ensures the output is too.
-/
@[inline] def instantiateRevS (e : Expr) (subst : Array Expr) : SymM Expr :=
  instantiateRevRangeS e 0 subst.size subst

/--
Similar to `Lean.Expr.instantiateRange`.
It assumes the input is maximally shared, and ensures the output is too.
It assumes `beginIdx ≤ endIdx` and `endIdx ≤ subst.size`
-/
def instantiateRangeS (e : Expr) (beginIdx endIdx : Nat) (subst : Array Expr) : SymM Expr :=
  if _ : beginIdx > endIdx then unreachable! else
  if _ : endIdx > subst.size then unreachable! else
  let s := beginIdx
  let n := endIdx - beginIdx
  replaceS e fun e offset => do
    let s₁ := s + offset
    match e with
    | .bvar idx =>
      if _h : idx >= s₁ then
        if _h : idx < s₁ + n then
          let v := subst[idx - s₁]
          liftLooseBVarsS' v 0 offset
        else
          Grind.mkBVarS (idx - n)
      else
        return some e
    | .lit _ | .mvar _ | .fvar _ | .const _ _ | .sort _ =>
      return some e
    | _ =>
      if s₁ >= e.looseBVarRange then
        return some e
      else
        return none

/--
Similar to `Lean.Expr.instantiate`.
It assumes the input is maximally shared, and ensures the output is too.
-/
def instantiateS (e : Expr) (subst : Array Expr) : SymM Expr :=
  instantiateRangeS e 0 subst.size subst

end Lean.Meta.Sym
