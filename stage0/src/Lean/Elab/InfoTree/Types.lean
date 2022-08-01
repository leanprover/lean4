/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Message
import Lean.Data.Json

namespace Lean.Elab

/-- Context after executing `liftTermElabM`.
   Note that the term information collected during elaboration may contain metavariables, and their
   assignments are stored at `mctx`. -/
structure ContextInfo where
  env           : Environment
  fileMap       : FileMap
  mctx          : MetavarContext := {}
  options       : Options        := {}
  currNamespace : Name           := Name.anonymous
  openDecls     : List OpenDecl  := []
  ngen          : NameGenerator -- We must save the name generator to implement `ContextInfo.runMetaM` and making we not create `MVarId`s used in `mctx`.
  deriving Inhabited

/-- An elaboration step -/
structure ElabInfo where
  elaborator : Name
  stx : Syntax
  deriving Inhabited

structure TermInfo extends ElabInfo where
  lctx : LocalContext -- The local context when the term was elaborated.
  expectedType? : Option Expr
  expr : Expr
  isBinder : Bool := false
  deriving Inhabited

structure CommandInfo extends ElabInfo where
  deriving Inhabited

inductive CompletionInfo where
  | dot (termInfo : TermInfo) (field? : Option Syntax) (expectedType? : Option Expr)
  | id (stx : Syntax) (id : Name) (danglingDot : Bool) (lctx : LocalContext) (expectedType? : Option Expr)
  | dotId (stx : Syntax) (id : Name) (lctx : LocalContext) (expectedType? : Option Expr)
  | fieldId (stx : Syntax) (id : Name) (lctx : LocalContext) (structName : Name)
  | namespaceId (stx : Syntax)
  | option (stx : Syntax)
  | endSection (stx : Syntax) (scopeNames : List String)
  | tactic (stx : Syntax) (goals : List MVarId)
  -- TODO `import`

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

structure CustomInfo where
  stx : Syntax
  json : Json
  deriving Inhabited

/-- An info that represents a user-widget.
User-widgets are custom pieces of code that run on the editor client.
You can learn about user widgets at `src/Lean/Widget/UserWidget`
-/
structure UserWidgetInfo where
  stx : Syntax
  /-- Id of `WidgetSource` object to use. -/
  widgetId : Name
  /-- Json representing the props to be loaded in to the component. -/
  props : Json
  deriving Inhabited

/-- Header information for a node in `InfoTree`. -/
inductive Info where
  | ofTacticInfo (i : TacticInfo)
  | ofTermInfo (i : TermInfo)
  | ofCommandInfo (i : CommandInfo)
  | ofMacroExpansionInfo (i : MacroExpansionInfo)
  | ofFieldInfo (i : FieldInfo)
  | ofCompletionInfo (i : CompletionInfo)
  | ofUserWidgetInfo (i : UserWidgetInfo)
  | ofCustomInfo (i : CustomInfo)
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
  | /-- The context object is created by `liftTermElabM` at `Command.lean` -/
    context (i : ContextInfo) (t : InfoTree)
  | /-- The children contain information for nested term elaboration and tactic evaluation -/
    node (i : Info) (children : Std.PersistentArray InfoTree)
  | /-- The elaborator creates holes (aka metavariables) for tactics and postponed terms -/
    hole (mvarId : MVarId)
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
  assignment : Std.PersistentHashMap MVarId InfoTree := {}
  /-- Pending child trees of a node. -/
  trees      : Std.PersistentArray InfoTree := {}
  deriving Inhabited

class MonadInfoTree (m : Type → Type)  where
  getInfoState    : m InfoState
  modifyInfoState : (InfoState → InfoState) → m Unit

export MonadInfoTree (getInfoState modifyInfoState)

instance [MonadLift m n] [MonadInfoTree m] : MonadInfoTree n where
  getInfoState      := liftM (getInfoState : m _)
  modifyInfoState f := liftM (modifyInfoState f : m _)

def setInfoState [MonadInfoTree m] (s : InfoState) : m Unit :=
  modifyInfoState fun _ => s

end Lean.Elab
