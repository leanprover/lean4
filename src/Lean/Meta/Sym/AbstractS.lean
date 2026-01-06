/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.ReplaceS
namespace Lean.Meta.Sym
open Internal

/--
Helper function for implementing `abstractFVars` (and possible variants in the future).
-/
@[inline] def abstractFVarsCore (e : Expr) (lctx : LocalContext)
    (maxFVar : PHashMap ExprPtr (Option FVarId))
    (minFVarId : FVarId) (toDeBruijn? : FVarId → Option Nat) : AlphaShareBuilderM Expr := do
  let minIndex := (lctx.find? minFVarId).get!.index
  replaceS' e fun e offset => do
    match e with
    | .fvar fvarId =>
      if let some bidx := toDeBruijn? fvarId then
        mkBVarS (offset + bidx)
      else
        return some e
    | .lit _ | .mvar _ | .bvar _ | .const _ _ | .sort _ =>
      /-
      Avoid `e.hasFVar` check.
      **Note**: metavariables are safe to skip because we assume their local contexts never include
      the free variables being abstracted (they were created before entering binders).
      -/
      return some e
    | _ =>
      -- Non-atomic expressions.
      if !e.hasFVar then
        -- Stop visiting: `e` does not contain free variables.
        return some e
      let some maxFVarId? := maxFVar.find? ⟨e⟩
        | return none -- maxFVar information is not available, keep visiting
      let maxIndex := (lctx.find? maxFVarId?.get!).get!.index
      if maxIndex < minIndex then
        -- Stop visiting: maximal free variable in `e` is smaller than minimal free variable being abstracted.
        return some e
      else
        -- Keep visiting
        return none

/--
Abstracts free variables `xs[start...*]` in expression `e`, converting them to de Bruijn indices.

Assumptions:
- The local context of the metavariables occurring in `e` do not include the free variables being
  abstracted. This invariant holds when abstracting over binders during pattern matching/unification:
  metavariables in the pattern were created before entering the binder, so their contexts exclude
  the bound variable's corresponding fvar.

- If `xs[start...*]` is not empty, then the minimal variable is `xs[start]`.

- Subterms whose `maxFVar` is below `minFVarId` are skipped entirely. This function does not assume
the `maxFVar` cache contains information for every subterm in `e`.
-/
public def abstractFVarsRange (e : Expr) (start : Nat) (xs : Array Expr) : SymM Expr := do
  if !e.hasFVar then return e
  if h : start < xs.size then
    let toDeBruijn? (fvarId : FVarId) : Option Nat :=
      let rec go (bidx : Nat) (i : Nat) (h : i < xs.size) : Option Nat :=
        if xs[i].fvarId! == fvarId then
          some bidx
        else if i > start then
          go (bidx + 1) (i - 1) (by omega)
        else
          none
      go 0 (xs.size - 1) (by omega)
    liftBuilderM <| abstractFVarsCore e (← getLCtx) (← get).maxFVar xs[start].fvarId! toDeBruijn?
  else
    return e

/--
Abstracts free variables `xs` in expression `e`, converting them to de Bruijn indices.

It is an abbreviation for `abstractFVarsRange e 0 xs`.
-/
public abbrev abstractFVars (e : Expr) (xs : Array Expr) : SymM Expr := do
  abstractFVarsRange e 0 xs

/--
Similar to `mkLambdaFVars`, but uses the more efficient `abstractFVars` and `abstractFVarsRange`,
and makes the same assumption made by these functions.
-/
public def mkLambdaFVarsS (xs : Array Expr) (e : Expr) : SymM Expr := do
  let b ← abstractFVars e xs
  xs.size.foldRevM (init := b) fun i _ b => do
    let x := xs[i]
    let decl ← x.fvarId!.getDecl
    let type ← abstractFVarsRange decl.type i xs
    mkLambdaS decl.userName decl.binderInfo type b

end Lean.Meta.Sym
