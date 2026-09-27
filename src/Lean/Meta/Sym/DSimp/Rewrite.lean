/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
public import Lean.Meta.Sym.DSimp.DSimproc
public import Lean.Meta.Sym.DSimp.Reduce
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.ACLt
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Tactic.Simp.SimpTheorems -- for `isRflTheorem`
import Init.Data.Range.Polymorphic.Iterators
namespace Lean.Meta.Sym.DSimp
open Lean.Meta.Sym.Simp (Theorem Theorems)

/-!
# Rewriting with `rfl`-theorems in `Sym.dsimp`

`Sym.dsimp` reuses the `Sym.simp` theorems, but only the ones proved by `rfl`, since a rewrite
step must hold by definitional equality. Theorems with hypotheses are never applied: there is
no discharger, and the instantiated hypotheses would have to be part of a proof term.
Definitions are unfolded by `unfold` instead of their equational theorems, which are rarely
`rfl`-theorems.
-/

/-- Tries to rewrite `e` using `thm`. -/
public def rewriteWith (thm : Theorem) (e : Expr) : DSimpM Result :=
  -- See the note about `withNewMCtxDepth` at `Simp.Theorem.rewrite`.
  withNewMCtxDepth do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let some result ← thm.pattern.match? e | return .rfl
  let mut args := result.args.toVector
  let us ← result.us.mapM instantiateLevelMVars
  for h : i in *...args.size do
    let arg := args[i]
    if let .mvar mvarId := arg then
      if (← mvarId.isAssigned) then
        args := args.set i (← instantiateMVarsS arg)
      else if (← mvarId.getDecl).index ≥ mvarCounterSaved then
        -- A hypothesis or instance not covered by the pattern. It cannot be discharged.
        return .rfl
    else if arg.hasMVar then
      args := args.set i (← instantiateMVarsS arg)
  let rhs := thm.rhs.instantiateLevelParams thm.pattern.levelParams us
  let rhs ← share rhs
  let e' ← instantiateRevBetaS rhs args.toArray
  if isSameExpr e e' then
    return .rfl
  if thm.perm && !(← acLt e' e) then
    return .rfl
  return .step e'

/-- Rewrites the prefix of `e` obtained by removing its last `numExtra` arguments. -/
private def rewriteOverApplied (thm : Theorem) (e : Expr) (numExtra : Nat) : DSimpM Result := do
  let f := e.getBoundedAppFn numExtra
  let .step f' _ ← rewriteWith thm f | return .rfl
  return .step (← share (mkAppN f' (e.getBoundedAppArgs numExtra)))

private def rewriteUsing (candidates : Array (Theorem × Nat)) (e : Expr) : DSimpM Result := do
  for (thm, numExtra) in candidates do
    let result ← if numExtra == 0 then rewriteWith thm e else rewriteOverApplied thm e numExtra
    if let .step .. := result then
      return result
  return .rfl

/--
Rewrites `e` using the first applicable theorem in `thms`. The fallback theorems
(`Theorem.fallback`) are tried only when no other theorem rewrites `e`.
-/
public def rewrite (thms : Theorems) : DSimproc := fun e => do
  let mctx ← getMCtx
  let result ← rewriteUsing (thms.getMatchWithExtra mctx e) e
  if let .rfl .. := result then
    unless thms.fallback.root.isEmpty do
      return (← rewriteUsing (thms.getFallbackMatchWithExtra mctx e) e)
  return result

/-- The `rfl`-theorems and the definitions to unfold contributed by `Sym.dsimp` parameters. -/
public structure Decls where
  thms     : Theorems := {}
  toUnfold : NameSet := {}

/--
Adds the declaration `declName` to `decls`. A theorem must be proved by `rfl`. A definition is
unfolded (see `unfold`) under the same conditions as in `Meta.simp` (`Simp.unfoldEvenWithEqns`),
and contributes its equational theorems proved by `rfl`. See also `Sym.Simp.getSimpTheoremNames`.
-/
public def Decls.add (decls : Decls) (declName : Name) : MetaM Decls := do
  let info ← getAsyncConstInfo declName
  if (← isProp info.sig.get.type) then
    unless (← isRflTheorem declName) do
      throwError "cannot use `{.ofConstName declName}` as a dsimp theorem, it is not proved by `rfl`"
    return { decls with thms := decls.thms.insert (← Sym.Simp.mkTheoremFromDecl declName) }
  let names ← Sym.Simp.getSimpTheoremNames declName
  let mut thms := decls.thms
  for name in names.thms do
    if (← isRflTheorem name) then
      thms := thms.insert (← Sym.Simp.mkTheoremFromDecl name)
  let mut toUnfold := decls.toUnfold
  if (← Lean.Meta.Simp.unfoldEvenWithEqns declName) then
    toUnfold := toUnfold.insert declName
  return { thms, toUnfold }

public def Decls.ofNames (declNames : Array Name) : MetaM Decls :=
  declNames.foldlM Decls.add {}

/-- The dsimproc unfolding the definitions and rewriting with the theorems in `decls`. -/
public def Decls.toDSimproc (decls : Decls) : DSimproc :=
  let p : DSimproc := if decls.toUnfold.isEmpty then fun _ => return .rfl else unfold decls.toUnfold
  if decls.thms.isEmpty then p else p >> rewrite decls.thms

end Lean.Meta.Sym.DSimp
