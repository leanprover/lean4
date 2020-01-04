/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.Definition

namespace Lean
namespace Elab
namespace Command

def expandOptDeclSig (stx : Syntax) : Syntax × Option Syntax :=
-- many Term.bracktedBinder >> Term.optType
let binders := stx.getArg 0;
let optType := stx.getArg 1; -- optional (parser! " : " >> termParser)
if optType.isNone then
  (binders, none)
else
  let typeSpec := optType.getArg 0;
  (binders, some $ typeSpec.getArg 1)

def expandDeclSig (stx : Syntax) : Syntax × Syntax :=
-- many Term.bracktedBinder >> Term.typeSpec
let binders := stx.getArg 0;
let typeSpec := stx.getArg 1;
(binders, typeSpec.getArg 1)

def elabAbbrev (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "abbrev " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `inline };
let modifiers       := modifiers.addAttribute { name := `reducible };
elabDefCore {
  ref := stx, kind := DefKind.def, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type := type, val := some (stx.getArg 3)
}

def elabDef (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "def " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
elabDefCore {
  ref := stx, kind := DefKind.def, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type := type,
  val := some (stx.getArg 3)
}

def elabTheorem (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "theorem " >> declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
elabDefCore {
  ref := stx, kind := DefKind.theorem, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type := some type, val := some (stx.getArg 3)
}

def elabConstant (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "constant " >> declId >> declSig >> optional declValSimple
let (binders, type) := expandDeclSig (stx.getArg 2);
elabDefCore {
  ref := stx, kind := DefKind.opaque, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type := some type, val := (stx.getArg 3).getOptional?
}

def elabInstance (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
-- parser! "instance " >> optional declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `instance };
declId ← match (stx.getArg 1).getOptional? with
  | some declId => pure declId
  | none        => throwError stx "not implemented yet";
elabDefCore {
  ref := stx, kind := DefKind.def, modifiers := modifiers,
  declId := declId, binders := binders, type := type, val := (stx.getArg 3).getOptional?
}

def elabAxiom (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "axiom " >> declId >> declSig
let (binders, type) := expandDeclSig (stx.getArg 2);
elabDefCore {
  ref := stx, kind := DefKind.axiom, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type := some type, val := none
}

def elabExample (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "example " >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 1);
let id              := mkIdentFrom stx `_example;
let declId          := Syntax.node `Lean.Parser.Command.declId #[id, mkNullNode];
elabDefCore {
  ref := stx, kind := DefKind.example, modifiers := modifiers,
  declId := declId, binders := binders, type := some type,
  val := some (stx.getArg 2)
}

def elabInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
pure () -- TODO

def elabClassInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
pure () -- TODO

def elabStructure (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
pure () -- TODO

@[builtinCommandElab declaration]
def elabDeclaration : CommandElab :=
fun stx => do
  modifiers ← elabModifiers (stx.getArg 0);
  let decl     := stx.getArg 1;
  let declKind := decl.getKind;
  if declKind == `Lean.Parser.Command.abbrev then
    elabAbbrev modifiers decl
  else if declKind == `Lean.Parser.Command.def then
    elabDef modifiers decl
  else if declKind == `Lean.Parser.Command.theorem then
    elabTheorem modifiers decl
  else if declKind == `Lean.Parser.Command.constant then
    elabConstant modifiers decl
  else if declKind == `Lean.Parser.Command.instance then
    elabInstance modifiers decl
  else if declKind == `Lean.Parser.Command.axiom then
    elabAxiom modifiers decl
  else if declKind == `Lean.Parser.Command.example then
    elabExample modifiers decl
  else if declKind == `Lean.Parser.Command.inductive then
    elabInductive modifiers decl
  else if declKind == `Lean.Parser.Command.classInductive then
    elabClassInductive modifiers decl
  else if declKind == `Lean.Parser.Command.structure then
    elabStructure modifiers decl
  else
    throwError stx.val "unexpected declaration"

end Command
end Elab
end Lean
