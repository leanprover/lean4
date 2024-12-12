/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Data.Position
import Lean.Data.OpenDecl
import Lean.MetavarContext
import Lean.Environment
import Lean.Data.Json
import Lean.Server.Rpc.Basic
import Lean.Widget.Types

namespace Lean.Elab

/--
Context after executing `liftTermElabM`.
Note that the term information collected during elaboration may contain metavariables, and their
assignments are stored at `mctx`.
-/
structure CommandContextInfo where
  env           : Environment
  fileMap       : FileMap
  mctx          : MetavarContext := {}
  options       : Options        := {}
  currNamespace : Name           := Name.anonymous
  openDecls     : List OpenDecl  := []
  ngen          : NameGenerator -- We must save the name generator to implement `ContextInfo.runMetaM` and making we not create `MVarId`s used in `mctx`.

/--
Context from the root of the `InfoTree` up to this node.
Note that the term information collected during elaboration may contain metavariables, and their
assignments are stored at `mctx`.
-/
structure ContextInfo extends CommandContextInfo where
  parentDecl? : Option Name := none

/--
Context for a sub-`InfoTree`.

Within `InfoTree`, this must fulfill the invariant that every non-`commandCtx` `PartialContextInfo`
node is always contained within a `commandCtx` node.
-/
inductive PartialContextInfo where
  | commandCtx (info : CommandContextInfo)
  /--
  Context for the name of the declaration that surrounds nodes contained within this `context` node.
  For example, this makes the name of the surrounding declaration available in `InfoTree` nodes
  corresponding to the terms within the declaration.
  -/
  | parentDeclCtx (parentDecl : Name)
  -- TODO: More constructors for the different kinds of scopes `commandCtx` is currently
  -- used for (e.g. eliminating `Info.updateContext?` would be nice!).

/-- Base structure for `TermInfo`, `CommandInfo` and `TacticInfo`. -/
structure ElabInfo where
  /-- The name of the elaborator that created this info. -/
  elaborator : Name
  /-- The piece of syntax that the elaborator created this info for.
  Note that this also implicitly stores the code position in the syntax's SourceInfo. -/
  stx : Syntax
  deriving Inhabited

structure TermInfo extends ElabInfo where
  lctx : LocalContext -- The local context when the term was elaborated.
  expectedType? : Option Expr
  expr : Expr
  isBinder : Bool := false
  deriving Inhabited

/--
Used instead of `TermInfo` when a term couldn't successfully be elaborated,
and so there is no complete expression available.

The main purpose of `PartialTermInfo` is to ensure that the sub-`InfoTree`s of a failed elaborator
are retained so that they can still be used in the language server.
-/
structure PartialTermInfo extends ElabInfo where
  lctx : LocalContext -- The local context when the term was elaborated.
  expectedType? : Option Expr
  deriving Inhabited

structure CommandInfo extends ElabInfo where
  deriving Inhabited

/-- A completion is an item that appears in the [IntelliSense](https://code.visualstudio.com/docs/editor/intellisense)
box that appears as you type. -/
inductive CompletionInfo where
  | dot (termInfo : TermInfo) (expectedType? : Option Expr)
  | id (stx : Syntax) (id : Name) (danglingDot : Bool) (lctx : LocalContext) (expectedType? : Option Expr)
  | dotId (stx : Syntax) (id : Name) (lctx : LocalContext) (expectedType? : Option Expr)
  | fieldId (stx : Syntax) (id : Option Name) (lctx : LocalContext) (structName : Name)
  | namespaceId (stx : Syntax)
  | option (stx : Syntax)
  | endSection (stx : Syntax) (scopeNames : List String)
  | tactic (stx : Syntax)
  -- TODO `import`

/-- Info for an option reference (e.g. in `set_option`). -/
structure OptionInfo where
  stx : Syntax
  optionName : Name
  declName : Name

structure FieldInfo where
  /-- Name of the projection. -/
  projName  : Name
  /-- Name of the field as written. -/
  fieldName : Name
  lctx      : LocalContext
  val       : Expr
  stx       : Syntax
  deriving Inhabited

/-- The information needed to render the tactic state in the infoview.

    We store the list of goals before and after the execution of a tactic.
    We also store the metavariable context at each time since we want metavariables
    unassigned at tactic execution time to be displayed as `?m...`. -/
structure TacticInfo extends ElabInfo where
  mctxBefore  : MetavarContext
  goalsBefore : List MVarId
  mctxAfter   : MetavarContext
  goalsAfter  : List MVarId
  deriving Inhabited

structure MacroExpansionInfo where
  lctx   : LocalContext -- The local context when the macro was expanded.
  stx    : Syntax
  output : Syntax
  deriving Inhabited

/-- Dynamic info for custom use cases. -/
structure CustomInfo where
  stx : Syntax
  value : Dynamic

/-- Information about a user widget associated with a syntactic span.
This must be a panel widget.
A panel widget is a widget that can be displayed
in the infoview alongside the goal state. -/
structure UserWidgetInfo extends Widget.WidgetInstance where
  stx : Syntax

/--
Specifies that the given free variables should be considered semantically identical.
The free variable `baseId` might not be in the current local context
because it has been cleared.
Used for e.g. connecting variables before and after `match` generalization.
-/
structure FVarAliasInfo where
  userName : Name
  id     : FVarId
  baseId : FVarId

/--
Contains the syntax of an identifier which is part of a field redeclaration, like:
```
structure Foo := x : Nat
structure Bar extends Foo :=
  x := 0
--^ here
```
-/
structure FieldRedeclInfo where
  stx : Syntax

/--
Denotes information for the term `⋯` that is emitted by the delaborator when omitting a term
due to `pp.deepTerms false` or `pp.proofs false`. Omission needs to be treated differently from regular terms because
it has to be delaborated differently in `Lean.Widget.InteractiveDiagnostics.infoToInteractive`:
Regular terms are delaborated explicitly, whereas omitted terms are simply to be expanded with
regular delaboration settings.
-/
structure OmissionInfo extends TermInfo where
  reason : String

/--
Indicates that all overloaded elaborators failed. The subtrees of a `ChoiceInfo` node are the
partial `InfoTree`s of those failed elaborators. Retaining these partial `InfoTree`s helps
the language server provide interactivity even when all overloaded elaborators failed.
-/
structure ChoiceInfo extends ElabInfo where

/-- Header information for a node in `InfoTree`. -/
inductive Info where
  | ofTacticInfo (i : TacticInfo)
  | ofTermInfo (i : TermInfo)
  | ofPartialTermInfo (i : PartialTermInfo)
  | ofCommandInfo (i : CommandInfo)
  | ofMacroExpansionInfo (i : MacroExpansionInfo)
  | ofOptionInfo (i : OptionInfo)
  | ofFieldInfo (i : FieldInfo)
  | ofCompletionInfo (i : CompletionInfo)
  | ofUserWidgetInfo (i : UserWidgetInfo)
  | ofCustomInfo (i : CustomInfo)
  | ofFVarAliasInfo (i : FVarAliasInfo)
  | ofFieldRedeclInfo (i : FieldRedeclInfo)
  | ofOmissionInfo (i : OmissionInfo)
  | ofChoiceInfo (i : ChoiceInfo)
  deriving Inhabited

/-- The InfoTree is a structure that is generated during elaboration and used
    by the language server to look up information about objects at particular points
    in the Lean document. For example, tactic information and expected type information in
    the infoview and information about completions.

    The infotree consists of nodes which may have child nodes. Each node
    has an `Info` object that contains details about what kind of information
    is present. Each `Info` object also contains a `Syntax` instance, this is used to
    map positions in the Lean document to particular info objects.

    An example of a function that extracts information from an infotree for a given
    position is `InfoTree.goalsAt?` which finds `TacticInfo`.

    Information concerning expressions requires that a context also be saved.
    `context` nodes store a local context that is used to process expressions
    in nodes below.

    Because the info tree is generated during elaboration, some parts of the infotree
    for a particular piece of syntax may not be ready yet. Hence InfoTree supports metavariable-like
    `hole`s which are filled in later in the same way that unassigned metavariables are.
-/
inductive InfoTree where
  /-- The context object is created at appropriate points during elaboration -/
  | context (i : PartialContextInfo) (t : InfoTree)
  /-- The children contain information for nested term elaboration and tactic evaluation -/
  | node (i : Info) (children : PersistentArray InfoTree)
  /-- The elaborator creates holes (aka metavariables) for tactics and postponed terms -/
  | hole (mvarId : MVarId)
  deriving Inhabited

/-- This structure is the state that is being used to build an InfoTree object.
During elaboration, some parts of the info tree may be `holes` which need to be filled later.
The `assignments` field is used to assign these holes.
The `trees` field is a list of pending child trees for the infotree node currently being built.

You should not need to use `InfoState` directly, instead infotrees should be built with the help of the methods here
such as `pushInfoLeaf` to create leaf nodes and `withInfoContext` to create a nested child node.

To see how `trees` is used, look at the function body of `withInfoContext'`.
-/
structure InfoState where
  /-- Whether info trees should be recorded. -/
  enabled    : Bool := true
  /-- Map from holes in the infotree to child infotrees. -/
  assignment : PersistentHashMap MVarId InfoTree := {}
  /-- Pending child trees of a node. -/
  trees      : PersistentArray InfoTree := {}
  deriving Inhabited

class MonadInfoTree (m : Type → Type) where
  getInfoState    : m InfoState
  modifyInfoState : (InfoState → InfoState) → m Unit

export MonadInfoTree (getInfoState modifyInfoState)

instance [MonadLift m n] [MonadInfoTree m] : MonadInfoTree n where
  getInfoState      := liftM (getInfoState : m _)
  modifyInfoState f := liftM (modifyInfoState f : m _)

def setInfoState [MonadInfoTree m] (s : InfoState) : m Unit :=
  modifyInfoState fun _ => s

class MonadParentDecl (m : Type → Type) where
  getParentDeclName? : m (Option Name)

export MonadParentDecl (getParentDeclName?)

end Lean.Elab
