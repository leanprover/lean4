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
-/
def mkRecAppWithSyntax (e : Expr) (stx : Syntax) : Expr :=
  mkMData (KVMap.empty.insert recAppKey (DataValue.ofSyntax stx)) e

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

namespace IgnoringRecApp

/-!
  We need variants of the app-destructuring functions that ignore the RecApp marker.
-/

open Expr

/--
  If the given expression is a sequence of
  function applications `f a₁ .. aₙ`, (ignoring rec app metadata) return `f`.
  Otherwise return the input expression.
-/
def getAppFn (e : Expr) : Expr :=
  match e with
  | app f _ => getAppFn f
  | mdata m b => if m.isRecApp then getAppFn b else e
  | _       => e

private def getAppNumArgsAux : Expr → Nat → Nat
  | app f _,   n => getAppNumArgsAux f (n+1)
  | mdata m b, n => if m.isRecApp then getAppNumArgsAux b n else n
  | _,         n => n

/-- Counts the number `n` of arguments for an expression `f a₁ .. aₙ` (ignoring
rec app metadata) -/
def getAppNumArgs (e : Expr) : Nat :=
  getAppNumArgsAux e 0

private def getAppArgsAux : Expr → Array Expr → Nat → Array Expr
  | app f a,   as, i => getAppArgsAux f (as.set! i a) (i-1)
  | mdata m b, as, i => if m.isRecApp then getAppArgsAux b as i else as
  | _,         as, _ => as

/-- Given `f a₁ a₂ ... aₙ` (ignoring rec app metatdaa), returns `#[a₁, ..., aₙ]` -/
@[inline] def getAppArgs (e : Expr) : Array Expr :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  getAppArgsAux e (mkArray nargs dummy) (nargs-1)

private def getAppRevArgsAux : Expr → Array Expr → Array Expr
  | app f a,   as => getAppRevArgsAux f (as.push a)
  | mdata m b, as => if m.isRecApp then getAppRevArgsAux b as else as
  | _,         as => as

/-- Same as `getAppArgs` but reverse the output array. -/
@[inline] def getAppRevArgs (e : Expr) : Array Expr :=
  getAppRevArgsAux e (Array.mkEmpty (getAppNumArgs e))

@[specialize] def withAppAux (k : Expr → Array Expr → α) : Expr → Array Expr → Nat → α
  | app f a,   as, i => withAppAux k f (as.set! i a) (i-1)
  | mdata m b, as, i => if m.isRecApp then withAppAux k b as i else k (mdata m b) as
  | f,         as, _ => k f as

/-- Given `e = f a₁ a₂ ... aₙ`, (ignoring rec app metadata) returns `k f #[a₁, ..., aₙ]`, but looks
through RecApp metadata. -/
@[inline] def withApp (e : Expr) (k : Expr → Array Expr → α) : α :=
  let dummy := mkSort levelZero
  let nargs := getAppNumArgs e
  withAppAux k e (mkArray nargs dummy) (nargs-1)

end IgnoringRecApp

end Lean
