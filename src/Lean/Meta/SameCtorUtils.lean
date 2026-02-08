/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Lean.Meta.Basic
import Lean.Meta.Transform

/-!
This module contains utilities for dealing with equalities between constructor applications,
in particular about which fields must be the same a-priori for the equality to type check.

Users include (or will include) the injectivity theorems, the per-constructor no-confusion
construction and deriving type classes lik `BEq`, `DecidableEq` or `Ord`.
-/

namespace Lean.Meta

/--
Returns true if `e` occurs either in `t`, or in the type of a sub-expression of `t`.

Consider the following example:
```lean
inductive Tyₛ : Type (u+1)
| SPi : (T : Type u) -> (T -> Tyₛ) -> Tyₛ

inductive Tmₛ.{u} :  Tyₛ.{u} -> Type (u+1)
| app : Tmₛ (.SPi T A) -> (arg : T) -> Tmₛ (A arg)```
```
When looking for fixed arguments in `Tmₛ.app`, if we only consider occurrences in the term `Tmₛ (A arg)`,
`T` is considered non-fixed despite the fact that `A : T -> Tyₛ`.
This leads to an ill-typed injectivity theorem signature:
```lean
theorem Tmₛ.app.inj {T : Type u} {A : T → Tyₛ} {a : Tmₛ (Tyₛ.SPi T A)} {arg : T} {T_1 : Type u} {a_1 : Tmₛ (Tyₛ.SPi T_1 A)} :
Tmₛ.app a arg = Tmₛ.app a_1 arg →
  T = T_1 ∧ a ≍ a_1 := fun x => Tmₛ.noConfusion x fun T_eq A_eq a_eq arg_eq => eq_of_heq a_eq
```
Instead of checking the type of every subterm, we only need to check the type of free variables, since free variables introduced in
the constructor may only appear in the type of other free variables introduced after them.
-/
public def occursOrInType (lctx : LocalContext) (e : Expr) (t : Expr) : Bool :=
  t.find? go |>.isSome
where
  go s := Id.run do
    let .fvar fvarId := s | s == e
    let some decl := lctx.find? fvarId | s == e
    return s == e || e.occurs decl.type

/--
Given a constructor, returns a mask of its fields, where `true` means that this field
occurs in the result type of the constructor.
-/
public def occursInCtorTypeMask (ctorName : Name) : MetaM (Array Bool) := do
  let ctorInfo ← getConstInfoCtor ctorName
  forallBoundedTelescope ctorInfo.type (some ctorInfo.numParams) fun _ ctorRet => do
    forallBoundedTelescope ctorRet (some ctorInfo.numFields) fun ys ctorRet => do
      let ctorRet ← whnf ctorRet
      let ctorRet ← Core.betaReduce ctorRet -- we 'beta-reduce' to eliminate "artificial" dependencies
      let lctx ← getLCtx
      return ys.map (occursOrInType lctx · ctorRet)

/--
Given a constructor (applied to the parameters already), brings its fields into scope twice,
but uses the same variable for fields that appear in the result type, so that the resulting
constructor applications have the same type.

Passes to `k`
* the new variables
* the indices to the type class
* the fields of the first constructor application
* the fields of the second constructor application
-/
public def withSharedCtorIndices (ctor : Expr)
    (k : Array Expr → Array Expr → Array Expr → Array Expr → MetaM α) : MetaM α := do
  let ctorType ← inferType ctor
  forallTelescopeReducing ctorType fun zs ctorRet => do
    let ctorRet ← whnf ctorRet
    let ctorRet ← Core.betaReduce ctorRet -- we 'beta-reduce' to eliminate "artificial" dependencies
    let indInfo ← getConstInfoInduct ctorRet.getAppFn.constName!
    let indices := ctorRet.getAppArgsN indInfo.numIndices

    let rec go zs2 mask todo acc := do
      match mask, todo with
      | true::mask', z::todo' =>
        go (zs2.push z) mask' todo' acc
      | false::mask', _::todo' =>
        let t ← whnfForall (← inferType (mkAppN ctor zs2))
        assert! t.isForall
        withLocalDeclD (t.bindingName!.appendAfter "'") t.bindingDomain! fun z' => do
          go (zs2.push z') mask' todo' (acc.push z')
      | _, _ =>
        k acc indices zs zs2

    let mask ← occursInCtorTypeMask ctor.getAppFn.constName!
    go #[] mask.toList zs.toList zs
