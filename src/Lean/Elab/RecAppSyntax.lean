/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean

private def recAppKey := `_recApp

/--
  We store the syntax at recursive applications to be able to generate better error messages
  when performing well-founded and structural recursion.

  We store it around the function, not the whole expression, so that the metadata
  does not get into the way of `e.withApp` and friends.
-/
def mkRecAppWithSyntax (e : Expr) (stx : Syntax) : Expr :=
  e.withApp fun f as =>
    let f' := mkMData (KVMap.empty.insert recAppKey (DataValue.ofSyntax stx)) f
    mkAppN f' as

/--
  Retrieve (if available) the syntax object attached to a recursive application.
-/
def getRecAppSyntax? (e : Expr) : Option Syntax :=
  match e with
  | Expr.mdata d _ =>
    match d.find recAppKey with
    | some (DataValue.ofSyntax stx) => some stx
    | _ => none
  | _                => none

/--
  Checks if the `MData` is for a recursive applciation.
-/
def MData.isRecApp (d : MData) : Bool :=
  d.contains recAppKey


/-- Given `f a₀ a₁ ... aₙ`, returns true if `f` is a constant with name `n` (possibly
wrapped with the RecApp marker) -/
def Expr.isRecAppOf (e : Expr) (n : Name) : Bool :=
  match e.getAppFn with
  | .const c _ => c == n
  | .mdata m (.const c _) => c == n && m.isRecApp
  | _           => false

/--
If the given expression is a sequence of
function applications `f a₁ .. aₙ` (possibly wrapped with the RecApp marker) return `f`.
Otherwise return the input expression.
-/
def Expr.getRecAppFn (e: Expr) : Expr :=
  match e with
  | .app f _ => f.getRecAppFn
  | .mdata m b => if m.isRecApp then b else e
  | _         => e

def Expr.withRecAppRef {m} [Monad m] [MonadRef m] {α} (e : Expr) (k : m α) : m α :=
  match getRecAppSyntax? e.getAppFn with
  | .some s => withRef s k
  | .none => k

end Lean
