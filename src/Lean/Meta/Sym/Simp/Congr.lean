/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Tactic.Grind.AlphaShareBuilder
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Simp.CongrInfo
namespace Lean.Meta.Sym.Simp
open Grind

/-!
# Simplifying Application Arguments and Congruence Lemma Application

This module provides functions for building congruence proofs during simplification.
Given a function application `f a₁ ... aₙ` where some arguments are rewritable,
we recursively simplify those arguments (via `simp`) and construct a proof that the
original expression equals the simplified one.

The key challenge is efficiency: we want to avoid repeatedly inferring types, or destroying sharing,
The `CongrInfo` type (see `SymM.lean`) categorizes functions
by their argument structure, allowing us to choose the most efficient proof strategy:

- `fixedPrefix`: Use simple `congrArg`/`congrFun'`/`congr` for trailing arguments. We exploit
  the fact that there are no dependent arguments in the suffix and use the cheaper `congrFun'`
  instead of `congrFun`.
- `interlaced`: Mix rewritable and fixed arguments. It may have to use `congrFun` for fixed
  dependent arguments.
- `congrTheorem`: Apply a pre-generated congruence theorem for dependent arguments

**Design principle**: Never infer the type of proofs. This avoids expensive type
inference on proof terms, which can be arbitrarily complex, and often destroys sharing.
-/

/--
Helper function for constructing a congruence proof using `congrFun'`, `congrArg`, `congr`.
For the dependent case, use `mkCongrFun`
-/
def mkCongr (e : Expr) (f a : Expr) (fr : Result) (ar : Result) (_ : e = .app f a) : SymM Result := do
  let mkCongrPrefix (declName : Name) : SymM Expr := do
    let α ← inferType a
    let u ← getLevel α
    let β ← inferType e
    let v ← getLevel β
    return mkApp2 (mkConst declName [u, v]) α β
  match isSameExpr fr.expr f, isSameExpr ar.expr a with
  | true,  true =>
    return { expr := e }
  | false, true =>
    let expr ← mkAppS fr.expr a
    let proof? := mkApp4 (← mkCongrPrefix ``congrFun') f fr.expr (← fr.getProof) a
    return { expr, proof? }
  | true, false =>
    let expr ← mkAppS f ar.expr
    let proof? := mkApp4 (← mkCongrPrefix ``congrArg) a ar.expr f (← ar.getProof)
    return { expr, proof? }
  | false, false =>
    let expr ← mkAppS fr.expr ar.expr
    let proof? := mkApp6 (← mkCongrPrefix ``congr) f fr.expr a ar.expr (← fr.getProof) (← ar.getProof)
    return { expr, proof? }

/--
Returns a proof using `congrFun`
```
congrFun.{u, v} {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (h : f = g) (a : α) : f a = g a
```
-/
def mkCongrFun (e : Expr) (f a : Expr) (fr : Result) (_ : e = .app f a) : SymM Result := do
  let .forallE x _ βx _ ← whnfD (← inferType f)
    | throwError "failed to build congruence proof, function expected{indentExpr f}"
  let α ← inferType a
  let u ← getLevel α
  let v ← getLevel (← inferType e)
  let β := Lean.mkLambda x .default α βx
  let expr ← mkAppS fr.expr a
  let proof? := mkApp6 (mkConst ``congrFun [u, v]) α β f fr.expr (← fr.getProof) a
  return { expr, proof? }

/--
Simplify arguments of a function application with a fixed prefix structure.
Recursively simplifies the trailing `suffixSize` arguments, leaving the first
`prefixSize` arguments unchanged.
-/
def congrFixedPrefix (e : Expr) (prefixSize : Nat) (suffixSize : Nat) : SimpM Result := do
  let numArgs := e.getAppNumArgs
  if numArgs ≤ prefixSize then
    -- Nothing to be done
    return { expr := e }
  else if numArgs > prefixSize + suffixSize then
    -- **TODO**: over-applied case
    return { expr := e }
  else
    go numArgs e
where
  go (i : Nat) (e : Expr) : SimpM Result := do
    if i == prefixSize then
      return { expr := e }
    else
      match h : e with
      | .app f a => mkCongr e f a (← go (i - 1) f) (← simp a) h
      | _ => unreachable!

/--
Simplify arguments of a function application with interlaced rewritable/fixed arguments.
Uses `rewritable[i]` to determine whether argument `i` should be simplified.
For rewritable arguments, calls `simp` and uses `congrFun'`, `congrArg`, and `congr`; for fixed arguments,
uses `congrFun` to propagate changes from earlier arguments.
-/
def congrInterlaced (e : Expr) (rewritable : Array Bool) : SimpM Result := do
  let numArgs := e.getAppNumArgs
  if h : numArgs = 0 then
    -- Nothing to be done
    return { expr := e }
  else if h : numArgs > rewritable.size then
    -- **TODO**: over-applied case
    return { expr := e }
  else
    go numArgs e (by omega)
where
  go (i : Nat) (e : Expr) (h : i ≤ rewritable.size) : SimpM Result := do
    if h : i = 0 then
      return { expr := e }
    else
      match h : e with
      | .app f a =>
        let fr ← go (i - 1) f (by omega)
        if rewritable[i - 1] then
          mkCongr e f a fr (← simp a) h
        else if isSameExpr fr.expr f then
          return { expr := e }
        else
          mkCongrFun e f a fr h
      | _ => unreachable!

/--
Simplify arguments using a pre-generated congruence theorem.
Used for functions with proof or `Decidable` arguments.
-/
def congrThm (e : Expr) (_ : CongrTheorem) : SimpM Result := do
  -- **TODO**
  return { expr := e }

/--
Main entry point for simplifying function application arguments.
Dispatches to the appropriate strategy based on the function's `CongrInfo`.
-/
public def congrArgs (e : Expr) : SimpM Result := do
  let f := e.getAppFn
  match (← getCongrInfo f) with
  | .none => return { expr := e }
  | .fixedPrefix prefixSize suffixSize => congrFixedPrefix e prefixSize suffixSize
  | .interlaced rewritable => congrInterlaced e rewritable
  | .congrTheorem thm => congrThm e thm

end Lean.Meta.Sym.Simp
