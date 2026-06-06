/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Expr

public section

namespace Lean

private def recAppKey := `_recApp
private def recAppPosKey := `_recAppPos

/--
We store the syntax at recursive applications to be able to generate better error messages
when performing well-founded and structural recursion.

We additionally store the source position as an extra key, so that two recursive applications
that are structurally identical as `Syntax` but originate from different source positions
still produce distinct `MData`. Otherwise hashconsing or simplification can merge them and
attribute an error to the wrong call site (issue #13444).
-/
def mkRecAppWithSyntax (e : Expr) (stx : Syntax) : Expr :=
  let m := KVMap.empty.insert recAppKey (.ofSyntax stx)
  let m := match stx.getPos? with
    | some p => m.insert recAppPosKey (.ofNat p.byteIdx)
    | none   => m
  mkMData m e

/--
Retrieve (if available) the syntax object attached to a recursive application.
-/
def getRecAppSyntax? (e : Expr) : Option Syntax :=
  match e with
  | .mdata d _ =>
    match d.find recAppKey with
    | some (DataValue.ofSyntax stx) => some stx
    | _ => none
  | _                => none

/--
Checks if the `MData` is for a recursive application.
-/
def MData.isRecApp (d : MData) : Bool :=
  d.contains recAppKey

/--
Return `true` if `getRecAppSyntax? e` is a `some`.
-/
def hasRecAppSyntax (e : Expr) : Bool :=
  match e with
  | .mdata d _ => d.isRecApp
  | _ => false

end Lean
