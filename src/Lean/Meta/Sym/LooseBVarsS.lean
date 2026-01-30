/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.ReplaceS
public section
namespace Lean.Meta.Sym
open Internal
/--
Lowers the loose bound variables `>= s` in `e` by `d`.
That is, a loose bound variable `bvar i` with `i >= s` is mapped to `bvar (i-d)`.
It assumes the input is maximally shared, and ensures the output is too.
Remark: if `s < d`, then the result is `e`.
-/
def lowerLooseBVarsS' (e : Expr) (s d : Nat) : AlphaShareBuilderM Expr := do
  replaceS' e fun e offset => do
    let s₁ := s + offset
    if s₁ >= e.looseBVarRange then
      return some e -- `e` does not contain bound variables with idx >= s₁
    else match e with
    | .bvar idx =>
      if idx >= s₁ then
        return some (← mkBVarS (idx - d))
      else
        return none
    | _ => return none

@[inherit_doc lowerLooseBVarsS']
def lowerLooseBVarsS (e : Expr) (s d : Nat) : SymM Expr :=
  liftBuilderM <| lowerLooseBVarsS' e s d

/--
Lifts loose bound variables `>= s` in `e` by `d`.
It assumes the input is maximally shared, and ensures the output is too.
-/
def liftLooseBVarsS' (e : Expr) (s d : Nat) : AlphaShareBuilderM Expr := do
  replaceS' e fun e offset => do
    let s₁ := s + offset
    if s₁ >= e.looseBVarRange then
      return some e -- `e` does not contain bound variables with idx >= s₁
    else match e with
    | .bvar idx =>
      if idx >= s₁ then
        return some (← mkBVarS (idx + d))
      else
        return none
    | _ => return none

@[inherit_doc liftLooseBVarsS']
def liftLooseBVarsS (e : Expr) (s d : Nat) : SymM Expr :=
  liftBuilderM <| liftLooseBVarsS' e s d

end Lean.Meta.Sym
