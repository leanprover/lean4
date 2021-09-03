/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Std.ShareCommon
import Lean.Parser.Command
import Lean.Util.CollectLevelParams
import Lean.Util.FoldConsts
import Lean.Meta.CollectFVars
import Lean.Elab.Command
import Lean.Elab.SyntheticMVars
import Lean.Elab.Binders
import Lean.Elab.DeclUtil
namespace Lean.Elab

inductive DefKind where
  | «def» | «theorem» | «example» | «opaque» | «abbrev»
  deriving Inhabited, BEq

def DefKind.isTheorem : DefKind → Bool
  | «theorem» => true
  | _         => false

def DefKind.isDefOrAbbrevOrOpaque : DefKind → Bool
  | «def»    => true
  | «opaque» => true
  | «abbrev» => true
  | _        => false

def DefKind.isExample : DefKind → Bool
  | «example» => true
  | _         => false

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

namespace MkInstanceName

-- Table for `mkInstanceName`
private def kindReplacements : NameMap String :=
  Std.RBMap.ofList [
    (``Parser.Term.depArrow, "DepArrow"),
    (``Parser.Term.«forall», "Forall"),
    (``Parser.Term.arrow, "Arrow"),
    (``Parser.Term.prop,  "Prop"),
    (``Parser.Term.sort,  "Sort"),
    (``Parser.Term.type,  "Type")
  ]

abbrev M := StateRefT String CommandElabM

def isFirst : M Bool :=
  return (← get) == ""

def append (str : String) : M Unit :=
  modify fun s => s ++ str

partial def collect (stx : Syntax) : M Unit := do
  match stx with
  | Syntax.node k args =>
    unless (← isFirst) do
      match kindReplacements.find? k with
      | some r => append r
      | none   => pure ()
    for arg in args do
      collect arg
  | Syntax.ident (preresolved := preresolved) .. =>
    unless preresolved.isEmpty && (← resolveGlobalName stx.getId).isEmpty do
      match stx.getId.eraseMacroScopes with
      | Name.str _ str _ =>
          if str[0].isLower then
            append str.capitalize
          else
            append str
      | _ => pure ()
  | _ => pure ()

def mkFreshInstanceName : CommandElabM Name := do
  let s ← get
  let idx := s.nextInstIdx
  modify fun s => { s with nextInstIdx := s.nextInstIdx + 1 }
  return Lean.Elab.mkFreshInstanceName s.env idx

partial def main (type : Syntax) : CommandElabM Name := do
  /- We use `expandMacros` to expand notation such as `x < y` into `LT.lt x y` -/
  let type ← liftMacroM <| expandMacros type
  let (_, str) ← collect type |>.run ""
  if str.isEmpty then
    mkFreshInstanceName
  else
    liftMacroM <| mkUnusedBaseName <| Name.mkSimple ("inst" ++ str)

end MkInstanceName

def mkDefViewOfConstant (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
  -- leading_parser "constant " >> declId >> declSig >> optional declValSimple
  let (binders, type) := expandDeclSig stx[2]
  let val ← match stx[3].getOptional? with
    | some val => pure val
    | none     =>
      let val ← `(arbitrary)
      pure $ Syntax.node ``Parser.Command.declValSimple #[ mkAtomFrom stx ":=", val ]
  return {
    ref := stx, kind := DefKind.opaque, modifiers := modifiers,
    declId := stx[1], binders := binders, type? := some type, value := val
  }

def mkDefViewOfInstance (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
  -- leading_parser Term.attrKind >> "instance " >> optNamedPrio >> optional declId >> declSig >> declVal
  let attrKind        ← liftMacroM <| toAttributeKind stx[0]
  let prio            ← liftMacroM <| expandOptNamedPrio stx[2]
  let attrStx         ← `(attr| instance $(quote prio):numLit)
  let (binders, type) := expandDeclSig stx[4]
  let modifiers       := modifiers.addAttribute { kind := attrKind, name := `instance, stx := attrStx }
  let declId ← match stx[3].getOptional? with
    | some declId => pure declId
    | none        =>
      let id ← MkInstanceName.main type
      pure <| Syntax.node ``Parser.Command.declId #[mkIdentFrom stx id, mkNullNode]
  return {
    ref := stx, kind := DefKind.def, modifiers := modifiers,
    declId := declId, binders := binders, type? := type, value := stx[5]
  }

def mkDefViewOfExample (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "example " >> declSig >> declVal
  let (binders, type) := expandDeclSig stx[1]
  let id              := mkIdentFrom stx `_example
  let declId          := Syntax.node ``Parser.Command.declId #[id, mkNullNode]
  { ref := stx, kind := DefKind.example, modifiers := modifiers,
    declId := declId, binders := binders, type? := some type, value := stx[2] }

def isDefLike (stx : Syntax) : Bool :=
  let declKind := stx.getKind
  declKind == ``Parser.Command.«abbrev» ||
  declKind == ``Parser.Command.«def» ||
  declKind == ``Parser.Command.«theorem» ||
  declKind == ``Parser.Command.«constant» ||
  declKind == ``Parser.Command.«instance» ||
  declKind == ``Parser.Command.«example»

def mkDefView (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView :=
  let declKind := stx.getKind
  if declKind == ``Parser.Command.«abbrev» then
    pure $ mkDefViewOfAbbrev modifiers stx
  else if declKind == ``Parser.Command.«def» then
    pure $ mkDefViewOfDef modifiers stx
  else if declKind == ``Parser.Command.«theorem» then
    pure $ mkDefViewOfTheorem modifiers stx
  else if declKind == ``Parser.Command.«constant» then
    mkDefViewOfConstant modifiers stx
  else if declKind == ``Parser.Command.«instance» then
    mkDefViewOfInstance modifiers stx
  else if declKind == ``Parser.Command.«example» then
    pure $ mkDefViewOfExample modifiers stx
  else
    throwError "unexpected kind of definition"

builtin_initialize registerTraceClass `Elab.definition

end Command
end Lean.Elab
