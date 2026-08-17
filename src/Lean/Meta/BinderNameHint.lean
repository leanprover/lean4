/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude

public import Lean.Meta.Basic

public section

namespace Lean


/-- Does `e` have a binder name hint? (quick check) -/
def Expr.hasBinderNameHint (e : Expr) : Bool :=
  Option.isSome <| e.find? fun e => e.isConstOf `binderNameHint

/-- A binder name, and whether a hint has named this binder already. -/
private abbrev Slot := Name × Bool

private def  enterScope (name : Name) (xs : Array Slot) : Array Slot :=
    xs.push (name, false)

private def exitScope (xs : Array Slot) : Name × Array Slot :=
    assert! xs.size > 0
    (xs.back!.1, xs.pop)

private def rememberName (bidx : Nat) (name : Name) (xs : Array Slot) : Array Slot :=
    assert! xs.size > bidx
    xs.set! (xs.size - bidx - 1) (name, true)

private def hintNamed (bidx : Nat) (xs : Array Slot) : Bool :=
    assert! xs.size > bidx
    xs[xs.size - bidx - 1]!.2

/--
Resolves occurrences of `binderNameHint` in `e`. See docstring of `binderNameHint` for more
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
  go (e : Expr) : MonadCacheT ExprStructEq Expr (StateT (Array Slot) CoreM) Expr := do
    checkCache { val := e : ExprStructEq } fun _ => do
      if e.isAppOfArity ``binderNameHint 6 then
        let v := e.appFn!.appFn!.appArg!
        let b := e.appFn!.appArg!
        let e := e.appArg!
        let e' ← go e
        match v, b.headBeta with
        | .bvar bidx, .lam n _ _ _
        | .bvar bidx, .forallE n _ _ _ =>
          -- A binder name with macro scopes is an implementation detail, not a user-facing name,
          -- so it does not overwrite the name an earlier hint remembered.
          unless n.hasMacroScopes && hintNamed bidx (← get) do
            modify (rememberName bidx n)
        | .bvar bidx, _ =>
          -- If we do not have a binder to use, ensure that name has macro scope.
          -- This is used by the well-founded definition preprocessor so that the new binder
          -- `fun h =>` has a macro-scope, and is inaccessible in the termination proof.
          -- (Using `fun _ =>` would show up as `property†` to appear, which is bad UX)
          let xs ← get
          assert! xs.size > bidx
          let n := xs[xs.size - bidx - 1]!.1
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
