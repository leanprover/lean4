/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Meta.ForEachExpr
import Lean.Elab.Command
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

section Snapshots
open Language

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
  tacStx? : Option Syntax
  /-- Incremental execution of main tactic block, if any. -/
  tacSnap? : Option (SnapshotTask Tactic.TacticParsedSnapshot)
  /-- Syntax of definition body, for checking reuse of `body`. -/
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

/-- State before elaboration of a definition header. -/
structure HeaderParsed where
  /--
  Input substring uniquely identifying header elaboration result given the same `Environment`.
  If missing, results should never be reused.
  -/
  headerSubstr? : Option Substring
  /-- Elaboration result, unless fatal exception occurred. -/
  processedSnap : SnapshotTask (Option HeaderProcessedSnapshot)
deriving Nonempty

/-- Snapshot after syntax tree has been split into separate mutual def headers. -/
structure HeadersParsedSnapshot extends Language.Snapshot where
  /-- Definition headers of this mutual block. -/
  headers : Array HeaderParsed
deriving Nonempty, TypeName
instance : Language.ToSnapshotTree HeadersParsedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, s.headers.map (·.processedSnap.map (sync := true) toSnapshotTree)⟩

end Snapshots

structure DefView where
  kind          : DefKind
  ref           : Syntax
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
  let modifiers       := modifiers.addAttribute { name := `inline }
  let modifiers       := modifiers.addAttribute { name := `reducible }
  { ref := stx, kind := DefKind.abbrev, modifiers,
    declId := stx[1], binders, type? := type, value := stx[3] }

def mkDefViewOfDef (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "def " >> declId >> optDeclSig >> declVal >> optDefDeriving
  let (binders, type) := expandOptDeclSig stx[2]
  let deriving? := if stx[4].isNone then none else some stx[4][1].getSepArgs
  { ref := stx, kind := DefKind.def, modifiers,
    declId := stx[1], binders, type? := type, value := stx[3], deriving? }

def mkDefViewOfTheorem (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "theorem " >> declId >> declSig >> declVal
  let (binders, type) := expandDeclSig stx[2]
  { ref := stx, kind := DefKind.theorem, modifiers,
    declId := stx[1], binders, type? := some type, value := stx[3] }

def mkFreshInstanceName : CommandElabM Name := do
  let s ← get
  let idx := s.nextInstIdx
  modify fun s => { s with nextInstIdx := s.nextInstIdx + 1 }
  return Lean.Elab.mkFreshInstanceName s.env idx

/--
  Generate a name for an instance with the given type.
  Note that we elaborate the type twice. Once for producing the name, and another when elaborating the declaration. -/
def mkInstanceName (binders : Array Syntax) (type : Syntax) : CommandElabM Name := do
  let savedState ← get
  try
    let result ← runTermElabM fun _ => Term.withAutoBoundImplicit <| Term.elabBinders binders fun _ => Term.withoutErrToSorry do
      let type ← instantiateMVars (← Term.elabType type)
      let ref ← IO.mkRef ""
      Meta.forEachExpr type fun e => do
        if e.isForall then ref.modify (· ++ "ForAll")
        else if e.isProp then ref.modify (· ++ "Prop")
        else if e.isType then ref.modify (· ++ "Type")
        else if e.isSort then ref.modify (· ++ "Sort")
        else if e.isConst then
          match e.constName!.eraseMacroScopes with
          | .str _ str =>
              if str.front.isLower then
                ref.modify (· ++ str.capitalize)
              else
                ref.modify (· ++ str)
          | _ => pure ()
      ref.get
    set savedState
    liftMacroM <| mkUnusedBaseName <| Name.mkSimple ("inst" ++ result)
  catch _ =>
    set savedState
    mkFreshInstanceName

def mkDefViewOfInstance (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
  -- leading_parser Term.attrKind >> "instance " >> optNamedPrio >> optional declId >> declSig >> declVal
  let attrKind        ← liftMacroM <| toAttributeKind stx[0]
  let prio            ← liftMacroM <| expandOptNamedPrio stx[2]
  let attrStx         ← `(attr| instance $(quote prio):num)
  let (binders, type) := expandDeclSig stx[4]
  let modifiers       := modifiers.addAttribute { kind := attrKind, name := `instance, stx := attrStx }
  let declId ← match stx[3].getOptional? with
    | some declId => pure declId
    | none        =>
      let id ← mkInstanceName binders.getArgs type
      pure <| mkNode ``Parser.Command.declId #[mkIdentFrom stx id, mkNullNode]
  return {
    ref := stx, kind := DefKind.def, modifiers := modifiers,
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
    ref := stx, kind := DefKind.opaque, modifiers := modifiers,
    declId := stx[1], binders := binders, type? := some type, value := val
  }

def mkDefViewOfExample (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "example " >> declSig >> declVal
  let (binders, type) := expandOptDeclSig stx[1]
  let id              := mkIdentFrom stx `_example
  let declId          := mkNode ``Parser.Command.declId #[id, mkNullNode]
  { ref := stx, kind := DefKind.example, modifiers := modifiers,
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

end Command
end Lean.Elab
