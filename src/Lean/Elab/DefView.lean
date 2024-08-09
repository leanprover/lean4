/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Elab.Command
import Lean.Elab.DeclNameGen
import Lean.Elab.DeclUtil

namespace Lean.Elab

inductive DefKind where
  | def | theorem | example | opaque | abbrev
  deriving Inhabited, BEq

def DefKind.isTheorem : DefKind → Bool
  | .theorem => true
  | _        => false

def DefKind.isDefOrAbbrevOrOpaque : DefKind → Bool
  | .def    => true
  | .opaque => true
  | .abbrev => true
  | _       => false

def DefKind.isExample : DefKind → Bool
  | .example => true
  | _        => false

/-- Header elaboration data of a `DefView`. -/
structure DefViewElabHeaderData where
  /--
    Short name. Recall that all declarations in Lean 4 are potentially recursive. We use `shortDeclName` to refer
    to them at `valueStx`, and other declarations in the same mutual block. -/
  shortDeclName : Name
  /-- Full name for this declaration. This is the name that will be added to the `Environment`. -/
  declName      : Name
  /-- Universe level parameter names explicitly provided by the user. -/
  levelNames    : List Name
  /-- Syntax objects for the binders occurring before `:`, we use them to populate the `InfoTree` when elaborating `valueStx`. -/
  binderIds     : Array Syntax
  /-- Number of parameters before `:`, it also includes auto-implicit parameters automatically added by Lean. -/
  numParams     : Nat
  /-- Type including parameters. -/
  type          : Expr
deriving Inhabited

section Snapshots
open Language

/-- Snapshot after processing of a definition body.  -/
structure BodyProcessedSnapshot extends Language.Snapshot where
  /-- State after elaboration. -/
  state : Term.SavedState
  /-- Elaboration result. -/
  value : Expr
deriving Nonempty
instance : Language.ToSnapshotTree BodyProcessedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[]⟩

/-- Snapshot after elaboration of a definition header. -/
structure HeaderProcessedSnapshot extends Language.Snapshot where
  /-- Elaboration results. -/
  view : DefViewElabHeaderData
  /-- Resulting elaboration state, including any environment additions. -/
  state : Term.SavedState
  /-- Syntax of top-level tactic block if any, for checking reuse of `tacSnap?`. -/
  tacStx? : Option Syntax
  /-- Incremental execution of main tactic block, if any. -/
  tacSnap? : Option (SnapshotTask Tactic.TacticParsedSnapshot)
  /-- Syntax of definition body, for checking reuse of `bodySnap`. -/
  bodyStx : Syntax
  /-- Result of body elaboration. -/
  bodySnap : SnapshotTask (Option BodyProcessedSnapshot)
deriving Nonempty
instance : Language.ToSnapshotTree HeaderProcessedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot,
    (match s.tacSnap? with
      | some tac => #[tac.map (sync := true) toSnapshotTree]
      | none     => #[]) ++
    #[s.bodySnap.map (sync := true) toSnapshotTree]⟩

/-- State before elaboration of a mutual definition. -/
structure DefParsed where
  /--
  Unstructured syntax object comprising the full "header" of the definition from the modifiers
  (incl. docstring) up to the value, used for determining header elaboration reuse.
  -/
  fullHeaderRef : Syntax
  /-- Elaboration result, unless fatal exception occurred. -/
  headerProcessedSnap : SnapshotTask (Option HeaderProcessedSnapshot)
deriving Nonempty

/-- Snapshot after syntax tree has been split into separate mutual def headers. -/
structure DefsParsedSnapshot extends Language.Snapshot where
  /-- Definitions of this mutual block. -/
  defs : Array DefParsed
deriving Nonempty, TypeName
instance : Language.ToSnapshotTree DefsParsedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot,
    s.defs.map (·.headerProcessedSnap.map (sync := true) toSnapshotTree)⟩

end Snapshots

structure DefView where
  kind          : DefKind
  ref           : Syntax
  /--
  An unstructured syntax object that comprises the "header" of the definition, i.e. everything up
  to the value. Used as a more specific ref for header elaboration.
  -/
  headerRef     : Syntax
  modifiers     : Modifiers
  declId        : Syntax
  binders       : Syntax
  type?         : Option Syntax
  value         : Syntax
  /--
  Snapshot for incremental processing of this definition.

  Invariant: If the bundle's `old?` is set, then elaboration of the header is guaranteed to result
  in the same elaboration result and state, i.e. reuse is possible.
  -/
  headerSnap?   : Option (Language.SnapshotBundle (Option HeaderProcessedSnapshot)) := none
  deriving?     : Option (Array Syntax) := none
  deriving Inhabited

def DefView.isInstance (view : DefView) : Bool :=
  view.modifiers.attrs.any fun attr => attr.name == `instance

namespace Command
open Meta

def mkDefViewOfAbbrev (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "abbrev " >> declId >> optDeclSig >> declVal
  let (binders, type) := expandOptDeclSig stx[2]
  let modifiers       := modifiers.addAttr { name := `inline }
  let modifiers       := modifiers.addAttr { name := `reducible }
  { ref := stx, headerRef := mkNullNode stx.getArgs[:3], kind := DefKind.abbrev, modifiers,
    declId := stx[1], binders, type? := type, value := stx[3] }

def mkDefViewOfDef (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "def " >> declId >> optDeclSig >> declVal >> optDefDeriving
  let (binders, type) := expandOptDeclSig stx[2]
  let deriving? := if stx[4].isNone then none else some stx[4][1].getSepArgs
  { ref := stx, headerRef := mkNullNode stx.getArgs[:3], kind := DefKind.def, modifiers,
    declId := stx[1], binders, type? := type, value := stx[3], deriving? }

def mkDefViewOfTheorem (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "theorem " >> declId >> declSig >> declVal
  let (binders, type) := expandDeclSig stx[2]
  { ref := stx, headerRef := mkNullNode stx.getArgs[:3], kind := DefKind.theorem, modifiers,
    declId := stx[1], binders, type? := some type, value := stx[3] }

def mkDefViewOfInstance (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
  -- leading_parser Term.attrKind >> "instance " >> optNamedPrio >> optional declId >> declSig >> declVal
  let attrKind        ← liftMacroM <| toAttributeKind stx[0]
  let prio            ← liftMacroM <| expandOptNamedPrio stx[2]
  let attrStx         ← withRef stx[1] `(attr| instance $(quote prio):num)
  let (binders, type) := expandDeclSig stx[4]
  let modifiers       := modifiers.addAttr { kind := attrKind, name := `instance, stx := attrStx }
  let declId ← match stx[3].getOptional? with
    | some declId =>
      if ← isTracingEnabledFor `Elab.instance.mkInstanceName then
        let id ← mkInstanceName binders.getArgs type
        trace[Elab.instance.mkInstanceName] "generated {(← getCurrNamespace) ++ id} for {declId}"
      pure declId
    | none        =>
      let id ← mkInstanceName binders.getArgs type
      trace[Elab.instance.mkInstanceName] "generated {(← getCurrNamespace) ++ id}"
      pure <| mkNode ``Parser.Command.declId #[mkIdentFrom stx id, mkNullNode]
  return {
    ref := stx, headerRef := mkNullNode stx.getArgs[:5], kind := DefKind.def, modifiers := modifiers,
    declId := declId, binders := binders, type? := type, value := stx[5]
  }

def mkDefViewOfOpaque (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
  -- leading_parser "opaque " >> declId >> declSig >> optional declValSimple
  let (binders, type) := expandDeclSig stx[2]
  let val ← match stx[3].getOptional? with
    | some val => pure val
    | none     =>
      let val ← if modifiers.isUnsafe then `(default_or_ofNonempty% unsafe) else `(default_or_ofNonempty%)
      `(Parser.Command.declValSimple| := $val)
  return {
    ref := stx, headerRef := mkNullNode stx.getArgs[:3], kind := DefKind.opaque, modifiers := modifiers,
    declId := stx[1], binders := binders, type? := some type, value := val
  }

def mkDefViewOfExample (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "example " >> declSig >> declVal
  let (binders, type) := expandOptDeclSig stx[1]
  let id              := mkIdentFrom stx `_example
  let declId          := mkNode ``Parser.Command.declId #[id, mkNullNode]
  { ref := stx, headerRef := mkNullNode stx.getArgs[:2], kind := DefKind.example, modifiers := modifiers,
    declId := declId, binders := binders, type? := type, value := stx[2] }

def isDefLike (stx : Syntax) : Bool :=
  let declKind := stx.getKind
  declKind == ``Parser.Command.abbrev ||
  declKind == ``Parser.Command.definition ||
  declKind == ``Parser.Command.theorem ||
  declKind == ``Parser.Command.opaque ||
  declKind == ``Parser.Command.instance ||
  declKind == ``Parser.Command.example

def mkDefView (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView :=
  let declKind := stx.getKind
  if declKind == ``Parser.Command.«abbrev» then
    return mkDefViewOfAbbrev modifiers stx
  else if declKind == ``Parser.Command.definition then
    return mkDefViewOfDef modifiers stx
  else if declKind == ``Parser.Command.theorem then
    return mkDefViewOfTheorem modifiers stx
  else if declKind == ``Parser.Command.opaque then
    mkDefViewOfOpaque modifiers stx
  else if declKind == ``Parser.Command.instance then
    mkDefViewOfInstance modifiers stx
  else if declKind == ``Parser.Command.example then
    return mkDefViewOfExample modifiers stx
  else
    throwError "unexpected kind of definition"

builtin_initialize registerTraceClass `Elab.definition
builtin_initialize registerTraceClass `Elab.instance.mkInstanceName

end Command
end Lean.Elab
