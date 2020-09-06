/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Std.ShareCommon
import Lean.Util.CollectLevelParams
import Lean.Util.FoldConsts
import Lean.Elab.CollectFVars
import Lean.Elab.Command
import Lean.Elab.SyntheticMVars
import Lean.Elab.Binders
import Lean.Elab.DeclUtil

namespace Lean
namespace Elab

inductive DefKind
| «def» | «theorem» | «example» | «opaque» | «abbrev»

def DefKind.isTheorem : DefKind → Bool
| DefKind.theorem => true
| _               => false

def DefKind.isDefOrAbbrevOrOpaque : DefKind → Bool
| DefKind.def    => true
| DefKind.opaque => true
| DefKind.abbrev => true
| _              => false

def DefKind.isExample : DefKind → Bool
| DefKind.example => true
| _               => false

structure DefView :=
(kind          : DefKind)
(ref           : Syntax)
(modifiers     : Modifiers)
(declId        : Syntax)
(binders       : Syntax)
(type?         : Option Syntax)
(value         : Syntax)

namespace Command

open Meta

def mkDefViewOfAbbrev (modifiers : Modifiers) (stx : Syntax) : DefView :=
-- parser! "abbrev " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `inline };
let modifiers       := modifiers.addAttribute { name := `reducible };
{ ref := stx, kind := DefKind.abbrev, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := type, value := stx.getArg 3 }

def mkDefViewOfDef (modifiers : Modifiers) (stx : Syntax) : DefView :=
-- parser! "def " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
{ ref := stx, kind := DefKind.def, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := type, value := stx.getArg 3 }

def mkDefViewOfTheorem (modifiers : Modifiers) (stx : Syntax) : DefView :=
-- parser! "theorem " >> declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
{ ref := stx, kind := DefKind.theorem, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := some type, value := stx.getArg 3 }

def mkFreshInstanceName : CommandElabM Name := do
s ← get;
let idx := s.nextInstIdx;
modify fun s => { s with nextInstIdx := s.nextInstIdx + 1 };
pure $ Lean.Elab.mkFreshInstanceName s.env idx

def mkDefViewOfConstant (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
-- parser! "constant " >> declId >> declSig >> optional declValSimple
let (binders, type) := expandDeclSig (stx.getArg 2);
val ← match (stx.getArg 3).getOptional? with
  | some val => pure val
  | none     => do {
    val ← `(arbitrary _);
    pure $ Syntax.node `Lean.Parser.Command.declValSimple #[ mkAtomFrom stx ":=", val ]
  };
pure {
  ref := stx, kind := DefKind.opaque, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := some type, value := val
}

def mkDefViewOfInstance (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
-- parser! "instance " >> optional declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `instance };
declId ← match (stx.getArg 1).getOptional? with
  | some declId => pure declId
  | none        => do {
    id ← mkFreshInstanceName;
    pure $ Syntax.node `Lean.Parser.Command.declId #[mkIdentFrom stx id, mkNullNode]
  };
pure {
  ref := stx, kind := DefKind.def, modifiers := modifiers,
  declId := declId, binders := binders, type? := type, value := stx.getArg 3
}

def mkDefViewOfExample (modifiers : Modifiers) (stx : Syntax) : DefView :=
-- parser! "example " >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 1);
let id              := mkIdentFrom stx `_example;
let declId          := Syntax.node `Lean.Parser.Command.declId #[id, mkNullNode];
{ ref := stx, kind := DefKind.example, modifiers := modifiers,
  declId := declId, binders := binders, type? := some type, value := stx.getArg 2 }

def isDefLike (stx : Syntax) : Bool :=
let declKind := stx.getKind;
declKind == `Lean.Parser.Command.«abbrev» ||
declKind == `Lean.Parser.Command.«def» ||
declKind == `Lean.Parser.Command.«theorem» ||
declKind == `Lean.Parser.Command.«constant» ||
declKind == `Lean.Parser.Command.«instance» ||
declKind == `Lean.Parser.Command.«example»

def mkDefView (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView :=
let declKind := stx.getKind;
if declKind == `Lean.Parser.Command.«abbrev» then
  pure $ mkDefViewOfAbbrev modifiers stx
else if declKind == `Lean.Parser.Command.«def» then
  pure $ mkDefViewOfDef modifiers stx
else if declKind == `Lean.Parser.Command.«theorem» then
  pure $ mkDefViewOfTheorem modifiers stx
else if declKind == `Lean.Parser.Command.«constant» then
  mkDefViewOfConstant modifiers stx
else if declKind == `Lean.Parser.Command.«instance» then
  mkDefViewOfInstance modifiers stx
else if declKind == `Lean.Parser.Command.«example» then
  pure $ mkDefViewOfExample modifiers stx
else
  throwError "unexpected kind of definition"

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.definition;
pure ()

end Command
end Elab
end Lean
