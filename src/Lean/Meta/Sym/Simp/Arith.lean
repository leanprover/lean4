/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Arith.Norm
public section
namespace Lean.Meta.Sym.Simp

private def isRelation (e : Expr) : Bool :=
  match_expr e with
  | Eq _ _ _ => true
  | LE.le _ _ _ _ => true
  | LT.lt _ _ _ _ => true
  | _ => false

/-- Caches `e` as a final result: it is a normal form, so a later visit costs a lookup. -/
private def cacheNormal (e : Expr) (cd : Bool) : SimpM Unit :=
  discard <| cacheResult e (mkRflResult (done := true) (contextDependent := cd))

/--
Given the normalized relation `e'` (with `h? : e = e'`, or `none` when `e'` is `e`), caches
its sides as normal forms, applies `post` to it, and chains the results.
-/
private def postRelation (e e' : Expr) (h? : Option Expr) (cd : Bool) : SimpM Result := do
  cacheNormal e'.appFn!.appArg! cd
  cacheNormal e'.appArg! cd
  match (← post e'), h? with
  | .rfl _ cd₂, none => return mkRflResult (done := true) (contextDependent := cd || cd₂)
  | .rfl _ cd₂, some h => return .step e' h (done := true) (contextDependent := cd || cd₂)
  | r₂, none => return if cd && !r₂.isContextDependent then r₂.withContextDependent else r₂
  | r₂, some h => mkEqTransResult e e' h r₂ cd

/--
Normalizes ring and semiring terms and relations into polynomial normal form
(`Sym.Arith.normalize?`), simplifying the atoms with `simp`. Intended as a `pre` simproc: it
sees the maximal arithmetic subtree first and reifies it once.

A normal form is final (`done := true`): `simp` does not re-enter it, so the normalizer never
runs on its own output, and it is cached so that reaching it again costs a lookup. Terms and
relations differ in what `post` sees:
* A normalized **term** is not visited by `post`. Rewrite rules on arithmetic operators are
  what the normalizer supersedes.
* A normalized **relation** (`=`, `≤`, `<`) is handed to `post` here, exactly once, and the
  result is chained in. This is how `t = t` and ground comparisons are closed
  (`evalGround`), and how rewrite rules on relations apply after normalization. Its two
  sides are cached as normal forms. If `post` rewrites the relation, that step is not final
  and `simp` continues on the result as usual.
-/
def simpArith : Simproc := fun e => do
  let r ← Arith.normalize? e simp
  match r with
  | .rfl true cd =>
    if isRelation e then postRelation e e none cd else return r
  | .step e' h true cd =>
    if isRelation e then
      postRelation e e' (some h) cd
    else
      cacheNormal e' cd
      return r
  | _ => return r

end Lean.Meta.Sym.Simp
