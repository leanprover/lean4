/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
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

structure DefView where
  kind          : DefKind
  ref           : Syntax
  modifiers     : Modifiers
  declId        : Syntax
  binders       : Syntax
  type?         : Option Syntax
  value         : Syntax
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
      pure <| mkNode ``Parser.Command.declValSimple #[ mkAtomFrom stx ":=", val ]
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
  declKind == ``Parser.Command.def ||
  declKind == ``Parser.Command.theorem ||
  declKind == ``Parser.Command.opaque ||
  declKind == ``Parser.Command.instance ||
  declKind == ``Parser.Command.example

def mkDefView (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView :=
  let declKind := stx.getKind
  if declKind == ``Parser.Command.«abbrev» then
    return mkDefViewOfAbbrev modifiers stx
  else if declKind == ``Parser.Command.def then
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
