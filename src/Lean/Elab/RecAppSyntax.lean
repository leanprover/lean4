/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr

namespace Lean

private def recAppCallerKey := `_recAppCaller
private def recAppSyntaxKey := `_recAppSyntax

/--
We store the syntax at recursive applications to be able to generate better error messages
when performing well-founded and structural recursion. We also store the current function name
so that we can match recursive calls to `decreasing_by` tactic in mutual recursion.
-/
def mkRecAppWithSyntax (e : Expr) (declName : Name) (stx : Syntax) : Expr :=
  let d := KVMap.empty |>.insert recAppSyntaxKey (.ofSyntax stx)
                       |>.insert recAppCallerKey (.ofName declName)
  mkMData d e

/--
Retrieve (if available) the syntax object attached to a recursive application.
-/
def getRecAppSyntax? (e : Expr) : Option (Name × Syntax) :=
  match e with
  | .mdata d _ =>
    match d.find recAppCallerKey, d.find recAppSyntaxKey with
    | some (.ofName n), some (.ofSyntax stx) => some (n, stx)
    | _, _ => none
  | _ => none

/--
Checks if the `MData` is for a recursive applciation.
-/
def MData.isRecApp (d : MData) : Bool :=
  d.contains recAppSyntaxKey && d.contains recAppCallerKey

/--
Return `true` if `getRecAppSyntax? e` is a `some`.
-/
def hasRecAppSyntax (e : Expr) : Bool :=
  match e with
  | .mdata d _ => d.isRecApp
  | _ => false

end Lean
