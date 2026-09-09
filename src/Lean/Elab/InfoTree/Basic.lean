/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Elab.InfoTree.Types
import Init.Data.Format.Macro
import Init.Data.Range.Polymorphic.Stream
import Init.Task
import Lean.Syntax

public section

namespace Lean.Elab

/--
Merges the `inner` partial context into the `outer` context s.t. fields of the `inner` context
overwrite fields of the `outer` context. Panics if the invariant described in the documentation
for `PartialContextInfo` is violated.

When traversing an `InfoTree`, this function should be used to combine the context of outer
nodes with the partial context of their subtrees. This ensures that the traversal has the context
from the inner node to the root node of the `InfoTree` available, with partial contexts of
inner nodes taking priority over contexts of outer nodes.
-/
def PartialContextInfo.mergeIntoOuter?
    : (inner : PartialContextInfo) → (outer? : Option ContextInfo) → Option ContextInfo
  | .commandCtx info, none =>
    some { info with }
  | .parentDeclCtx _, none =>
    panic! "Unexpected incomplete InfoTree context info."
  | .autoImplicitCtx _, none =>
    panic! "Unexpected incomplete InfoTree context info."
  | .commandCtx innerInfo, some outer =>
    some { outer with toCommandContextInfo := { innerInfo with cmdEnv? := outer.cmdEnv? <|> innerInfo.cmdEnv? } }
  | .parentDeclCtx innerParentDecl, some outer =>
    some { outer with parentDecl? := innerParentDecl }
  | .autoImplicitCtx innerAutoImplicits, some outer =>
    some { outer with autoImplicits := innerAutoImplicits }

def CompletionInfo.stx : CompletionInfo → Syntax
  | dot i ..          => i.stx
  | id stx ..         => stx
  | dotId stx ..      => stx
  | fieldId stx ..    => stx
  | namespaceId stx   => stx
  | option stx        => stx
  | errorName stx ..  => stx
  | endSection stx .. => stx
  | tactic stx ..     => stx

/--
Obtains the `LocalContext` from this `CompletionInfo` if available and yields an empty context
otherwise.
-/
def CompletionInfo.lctx : CompletionInfo → LocalContext
  | dot i ..            => i.lctx
  | id _ _ _ lctx ..    => lctx
  | dotId _ _ lctx ..   => lctx
  | fieldId _ _ lctx .. => lctx
  | _                   => .empty

partial def InfoTree.findInfo? (p : Info → Bool) (t : InfoTree) : Option Info :=
  match t with
  | context _ t => findInfo? p t
  | node i ts   =>
    if p i then
      some i
    else
      ts.findSome? (findInfo? p)
  | _ => none

/-- Instantiate the holes on the given `tree` with the assignment table.
(analogous to instantiating the metavariables in an expression) -/
partial def InfoTree.substitute (tree : InfoTree) (assignment : PersistentHashMap MVarId InfoTree) : InfoTree :=
  match tree with
  | node i c => node i <| c.map (substitute · assignment)
  | context i t => context i (substitute t assignment)
  | hole id  => match assignment.find? id with
    | none      => hole id
    | some tree => substitute tree assignment

/-- Applies `s.lazyAssignment` to `s.trees`, asynchronously. -/
def InfoState.substituteLazy (s : InfoState) : Task InfoState :=
  Task.mapList (tasks := s.lazyAssignment.toList.map (·.2)) fun _ => { s with
    trees := s.trees.map (·.substitute <| s.lazyAssignment.map (·.get))
    lazyAssignment := {}
  }

structure LinterInfoGroup where
  deriving TypeName

def mkLinterInfoGroupNode (trees : PersistentArray InfoTree) : InfoTree :=
  InfoTree.node (Info.ofCustomInfo { stx := .missing, value := Dynamic.mk (⟨⟩ : LinterInfoGroup) }) trees

def pushInfoChild : InfoTree → InfoTree → InfoTree
  | .context ctx (.node i cs), child => .context ctx (.node i (cs.push child))
  | t, _ => t

def Info.toElabInfo? : Info → Option ElabInfo
  | ofTacticInfo i         => some i.toElabInfo
  | ofTermInfo i           => some i.toElabInfo
  | ofPartialTermInfo i    => some i.toElabInfo
  | ofCommandInfo i        => some i.toElabInfo
  | ofMacroExpansionInfo _ => none
  | ofOptionInfo _         => none
  | ofErrorNameInfo _      => none
  | ofFieldInfo _          => none
  | ofCompletionInfo _     => none
  | ofUserWidgetInfo _     => none
  | ofCustomInfo _         => none
  | ofFVarAliasInfo _      => none
  | ofFieldRedeclInfo _    => none
  | ofDelabTermInfo i      => some i.toElabInfo
  | ofChoiceInfo i         => some i.toElabInfo
  | ofDocInfo i            => some i.toElabInfo
  | ofDocElabInfo i        => some i.toElabInfo

/--
  Helper function for propagating the tactic metavariable context to its children nodes.
  We need this function because we preserve `TacticInfo` nodes during backtracking *and* their
  children. Moreover, we backtrack the metavariable context to undo metavariable assignments.
  `TacticInfo` nodes save the metavariable context before/after the tactic application, and
  can be pretty printed without any extra information. This is not the case for `TermInfo` nodes.
  Without this function, the formatting method would often fail when processing `TermInfo` nodes
  that are children of `TacticInfo` nodes that have been preserved during backtracking.
  Saving the metavariable context at `TermInfo` nodes is also not a good option because
  at `TermInfo` creation time, the metavariable context often miss information, e.g.,
  a TC problem has not been resolved, a postponed subterm has not been elaborated, etc.

  See `Term.SavedState.restore`.
-/
def Info.updateContext? : Option ContextInfo → Info → Option ContextInfo
  | some ctx, ofTacticInfo i => some { ctx with mctx := i.mctxAfter }
  | ctx?, _ => ctx?

def Info.stx : Info → Syntax
  | ofTacticInfo i         => i.stx
  | ofTermInfo i           => i.stx
  | ofPartialTermInfo i    => i.stx
  | ofCommandInfo i        => i.stx
  | ofMacroExpansionInfo i => i.stx
  | ofOptionInfo i         => i.stx
  | ofErrorNameInfo i      => i.stx
  | ofFieldInfo i          => i.stx
  | ofCompletionInfo i     => i.stx
  | ofCustomInfo i         => i.stx
  | ofUserWidgetInfo i     => i.stx
  | ofFVarAliasInfo _      => .missing
  | ofFieldRedeclInfo i    => i.stx
  | ofDelabTermInfo i      => i.stx
  | ofChoiceInfo i         => i.stx
  | ofDocInfo i            => i.stx
  | ofDocElabInfo i        => i.stx

private def CompletionInfo.setStx (stx : Syntax) : CompletionInfo → CompletionInfo
  | dot i e?              => .dot { i with stx } e?
  | id _ n dd lctx e?     => .id stx n dd lctx e?
  | dotId _ n lctx e?     => .dotId stx n lctx e?
  | fieldId _ n? lctx s   => .fieldId stx n? lctx s
  | namespaceId _         => .namespaceId stx
  | option _              => .option stx
  | errorName _ pid       => .errorName stx pid
  | endSection _ n? dd ns => .endSection stx n? dd ns
  | tactic _              => .tactic stx

private def Info.setStx (stx : Syntax) : Info → Info
  | ofTacticInfo i         => ofTacticInfo { i with stx }
  | ofTermInfo i           => ofTermInfo { i with stx }
  | ofPartialTermInfo i    => ofPartialTermInfo { i with stx }
  | ofCommandInfo i        => ofCommandInfo { i with stx }
  | ofMacroExpansionInfo i => ofMacroExpansionInfo { i with stx }
  | ofOptionInfo i         => ofOptionInfo { i with stx }
  | ofErrorNameInfo i      => ofErrorNameInfo { i with stx }
  | ofFieldInfo i          => ofFieldInfo { i with stx }
  | ofCompletionInfo i     => ofCompletionInfo (i.setStx stx)
  | ofCustomInfo i         => ofCustomInfo { i with stx }
  | ofUserWidgetInfo i     => ofUserWidgetInfo { i with stx }
  | ofFVarAliasInfo i      => ofFVarAliasInfo i
  | ofFieldRedeclInfo i    => ofFieldRedeclInfo { i with stx }
  | ofDelabTermInfo i      => ofDelabTermInfo { i with stx }
  | ofChoiceInfo i         => ofChoiceInfo { i with stx }
  | ofDocInfo i            => ofDocInfo { i with stx }
  | ofDocElabInfo i        => ofDocElabInfo { i with stx }

/--
Adds the given trailing substring to all adjacent syntax in the info tree if any, otherwise returns
`none`.
-/
partial def InfoTree.addTrailing? (trailing : Substring.Raw) : Elab.InfoTree → Option Elab.InfoTree
  | .context i t => t.addTrailing? trailing |>.map (.context i)
  | .node info children => Id.run do
    let stx? := info.stx.addTrailing? trailing
    -- NOTE: we need to visit the children even if `stx` was not actually changed as info trees are
    -- not necessarily properly nested regarding syntax ranges!
    let childTrailing := (stx?.getD info.stx).getTrailing?.getD trailing
    let mut changed := false
    let mut newChildren := children
    for c in children, i in 0...* do
      if let some c' := c.addTrailing? childTrailing then
        changed := true
        newChildren := newChildren.set i c'
    if stx?.isNone && !changed then
      return none
    let info := match stx? with
      | some stx => info.setStx stx
      | none     => info
    return some (.node info newChildren)
  | .hole _ => none

/-- Adds the given trailing substring to all adjacent syntax in the info tree. -/
def InfoTree.addTrailing (trailing : Substring.Raw) (t : Elab.InfoTree) : Elab.InfoTree :=
  t.addTrailing? trailing |>.getD t
