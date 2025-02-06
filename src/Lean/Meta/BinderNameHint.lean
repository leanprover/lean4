/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Lean.Util.FindExpr
import Lean.Meta.Basic
import Init.BinderNameHint

namespace Lean


/-- Does `e` have a binder name hint? (quick check) -/
def Expr.hasBinderNameHint (e : Expr) : Bool :=
  Option.isSome <| e.find? fun e => e.isConstOf `binderNameHint

private def  enterScope (name : Name) (xs : Array Name) : Array Name :=
    xs.push name

private def exitScope (xs : Array Name) : Name × Array Name :=
    assert! xs.size > 0
    (xs.back!, xs.pop)

private def rememberName (bidx : Nat) (name : Name) (xs : Array Name) : Array Name :=
    assert! xs.size > bidx
    xs.set! (xs.size - bidx - 1) name

private def makeFresh (bidx : Nat) (xs : Array Name) : CoreM (Array Name) := do
    assert! xs.size > bidx
    let name := xs[xs.size - bidx - 1]!
    let name' ← Core.mkFreshUserName name
    return xs.set! (xs.size - bidx - 1) name'

/--
Resovles occurrences of `binderNameHint` in `e`. See docstring of `binderNameHint` for more
information.
-/
partial def Expr.resolveBinderNameHint (e : Expr) : CoreM Expr :=
  (go e).run.run' #[]
where
/-
Implementation note:

We traverse the expression as an open term; we do not need a local context here.

The state is the array of binder names. The length of the array is always the binder nesting depth,
and the innermost binder is at the end. We update the binder names therein when encountering a
`binderNameHint`, and update the binder when exiting the scope.
-/
  go (e : Expr) : MonadCacheT ExprStructEq Expr (StateT (Array Name) CoreM) Expr := do
    checkCache { val := e : ExprStructEq } fun _ => do
      if e.isAppOfArity `binderNameHint 6 then
        let v := e.appFn!.appFn!.appArg!
        let b := e.appFn!.appArg!
        let e := e.appArg!
        let e' ← go e
        match v, b.headBeta with
        | .bvar bidx, .lam n _ _ _
        | .bvar bidx, .forallE n _ _ _ =>
          modify (rememberName bidx n)
        | .bvar bidx, _ =>
          -- If we do not have a binder to use, ensure that name has macro scope.
          -- This is used by the auto-attach lemmas so that the new binder `fun h =>`
          -- has a macro-scope, and is inaccessible in the termination proof.
          -- (Using `fun _ =>` causes `property†` to appear, which is bad UX)
          let xs ← get
          assert! xs.size > bidx
          let n := xs[xs.size - bidx - 1]!
          let n' ← mkFreshUserName n
          modify (rememberName bidx n')
        | _, _ =>
          pure ()
        pure e'
      else
        match e with
        | .forallE n d b bi =>
          let d' ← go d
          modify (enterScope n)
          let b' ← go b
          let n' ← modifyGet exitScope
          return .forallE n' d' b' bi
        | .lam n d b bi =>
          let d' ← go d
          modify (enterScope n)
          let b' ← go b
          let n' ← modifyGet exitScope
          return .lam n' d' b' bi
        | .letE n t v b nd  =>
          let t' ← go t
          let v' ← go v
          modify (enterScope n)
          let b' ← go b
          let n' ← modifyGet exitScope
          return .letE n' t' v' b' nd
        | .app f a         => return e.updateApp! (← go f) (← go a)
        | .mdata _ b       => return e.updateMData! (← go b)
        | .proj _ _ b      => return e.updateProj! (← go b)
        | _                => return e

end Lean
