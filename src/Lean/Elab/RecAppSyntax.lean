/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Data.String.Substring
public import Lean.Expr

public section

namespace Lean

private def recAppKey := `_recApp
private def recAppPosKey := `_recAppPos

private def detachSourceInfo : SourceInfo → SourceInfo
  | .original _ pos _ endPos => .synthetic pos endPos (canonical := true)
  | info => info

/--
Copy of `stx` that does not reference the input string: every `SourceInfo.original` becomes a
`SourceInfo.synthetic` with the same range, and identifiers get a fresh copy of their raw value.

The syntax stored at a recursive application lives inside an `Expr`, so `Expr` traversals that
follow every pointer (e.g. `ShareCommon.shareCommon'`) visit it too. The `leading` and `trailing`
substrings of `SourceInfo.original` and the `rawVal` of identifiers all share the whole input
string, so storing `stx` itself would make such traversals visit, and hash, the input string once
per substring. With thousands of recursive definitions in a file, this dominates elaboration time.

We keep the syntax tree instead of just its source range because error messages print the
recursive call (see `PartialFixpoint`), and syntax produced by quotations may not have a position
to recover the text from.
-/
private partial def detachSyntax : Syntax → Syntax
  | .node info kind args => .node (detachSourceInfo info) kind (args.map detachSyntax)
  | .atom info val => .atom (detachSourceInfo info) val
  | .ident info rawVal val pre => .ident (detachSourceInfo info) rawVal.toString.toRawSubstring val pre
  | .missing => .missing

/--
We store the syntax at recursive applications to be able to generate better error messages
when performing well-founded and structural recursion. The stored syntax is detached from the
input string, see `detachSyntax`.

We additionally store the source position as an extra key, so that two recursive applications
that are structurally identical as `Syntax` but originate from different source positions
still produce distinct `MData`. Otherwise hashconsing or simplification can merge them and
attribute an error to the wrong call site (issue #13444).
-/
def mkRecAppWithSyntax (e : Expr) (stx : Syntax) : Expr :=
  let stx := detachSyntax stx
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
