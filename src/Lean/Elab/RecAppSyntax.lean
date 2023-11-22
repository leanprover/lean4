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

end Lean
