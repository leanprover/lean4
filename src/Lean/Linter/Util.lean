/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

prelude
public import Lean.Server.InfoUtils
public import Lean.Linter.Init
public import Lean.Elab.Term

public section

namespace Lean.Linter

open Lean.Elab

/-- Go upwards through the given `tree` starting from the smallest node that
contains the given `range` and collect all `MacroExpansionInfo`s on the way up.
The result is `some []` if no `MacroExpansionInfo` was found on the way and
`none` if no `InfoTree` node was found that covers the given `range`.

Return the result reversed, s.t. the macro expansion that would be applied to
the original syntax first is the first element of the returned list. -/
def collectMacroExpansions? {m} [Monad m] (range : Lean.Syntax.Range) (tree : Elab.InfoTree) : m <| Option <| List Elab.MacroExpansionInfo := do
  if let .some <| .some result ← go then
    return some result.reverse
  else
    return none
where
  go : m <| Option <| Option <| List Elab.MacroExpansionInfo := tree.visitM (postNode := fun _ i _ results => do
    let results := results |>.filterMap id |>.filterMap id

    -- we expect that at most one InfoTree child returns a result
    if let results :: _ := results then
      if let .ofMacroExpansionInfo i := i then
        return some <| i :: results
      else
        return some results
    else if i.contains range.start && i.contains (includeStop := true) range.stop then
      if let .ofMacroExpansionInfo i := i then
        return some [i]
      else
        return some []
    else
      return none)

/-- Get the `parentDecl`s of every elaborated body in the infotree. -/
def getDeclsByBody (t : InfoTree) : List Name :=
  t.collectNodesBottomUp fun ctx i _ decls =>
    match i with
    | .ofCustomInfo i =>
      if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
        if let some decl := ctx.parentDecl? then
          decl :: decls
        else decls
      else decls
    | _ => decls

/-- Get the names of declarations introduced by elaborating `t`.

A declaration introduces a `TermInfo` with `isBinder := true` whose `expr` is the constant
being declared. This covers `def`/`theorem`/`axiom`, inductive types and their constructors,
and structure fields and parent projections — including mutual blocks where each member
emits its own binder.
-/
def getNewDecls (t : InfoTree) : List Name :=
  t.collectNodesBottomUp fun _ i _ acc =>
    match i with
    | .ofTermInfo ti =>
      if ti.isBinder && ti.expr.isConst then
        ti.expr.constName! :: acc
      else
        acc
    | _ => acc
