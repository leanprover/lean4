/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectLevelParams
import Lean.Elab.Definition
import Lean.Elab.Inductive

namespace Lean
namespace Elab
namespace Command

def expandOptDeclSig (stx : Syntax) : Syntax × Option Syntax :=
-- many Term.bracketedBinder >> Term.optType
let binders := stx.getArg 0;
let optType := stx.getArg 1; -- optional (parser! " : " >> termParser)
if optType.isNone then
  (binders, none)
else
  let typeSpec := optType.getArg 0;
  (binders, some $ typeSpec.getArg 1)

def expandDeclSig (stx : Syntax) : Syntax × Syntax :=
-- many Term.bracketedBinder >> Term.typeSpec
let binders := stx.getArg 0;
let typeSpec := stx.getArg 1;
(binders, typeSpec.getArg 1)

def elabAbbrev (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "abbrev " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `inline };
let modifiers       := modifiers.addAttribute { name := `reducible };
elabDefLike {
  ref := stx, kind := DefKind.abbrev, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := type, val := stx.getArg 3
}

def elabDef (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "def " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
elabDefLike {
  ref := stx, kind := DefKind.def, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := type, val := stx.getArg 3
}

def elabTheorem (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "theorem " >> declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
elabDefLike {
  ref := stx, kind := DefKind.theorem, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := some type, val := stx.getArg 3
}

def elabConstant (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
-- parser! "constant " >> declId >> declSig >> optional declValSimple
let (binders, type) := expandDeclSig (stx.getArg 2);
val ← match (stx.getArg 3).getOptional? with
  | some val => pure val
  | none     => do {
    val ← `(arbitrary _);
    pure $ Syntax.node `Lean.Parser.Command.declValSimple #[ mkAtomFrom stx ":=", val ]
  };
elabDefLike {
  ref := stx, kind := DefKind.opaque, modifiers := modifiers,
  declId := stx.getArg 1, binders := binders, type? := some type, val := val
}

def elabInstance (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
-- parser! "instance " >> optional declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `instance };
declId ← match (stx.getArg 1).getOptional? with
  | some declId => pure declId
  | none        => throwError stx "not implemented yet";
elabDefLike {
  ref := stx, kind := DefKind.def, modifiers := modifiers,
  declId := declId, binders := binders, type? := type, val := stx.getArg 3
}

def elabExample (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "example " >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 1);
let id              := mkIdentFrom stx `_example;
let declId          := Syntax.node `Lean.Parser.Command.declId #[id, mkNullNode];
elabDefLike {
  ref := stx, kind := DefKind.example, modifiers := modifiers,
  declId := declId, binders := binders, type? := some type, val := stx.getArg 2
}

def elabAxiom (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
-- parser! "axiom " >> declId >> declSig
let declId             := stx.getArg 1;
let (binders, typeStx) := expandDeclSig (stx.getArg 2);
scopeLevelNames ← getLevelNames;
withDeclId declId $ fun name => do
  declName          ← mkDeclName declId modifiers name;
  applyAttributes stx declName modifiers.attrs AttributeApplicationTime.beforeElaboration;
  allUserLevelNames ← getLevelNames;
  decl ← runTermElabM declName $ fun vars => Term.elabBinders binders.getArgs $ fun xs => do {
    type ← Term.elabType typeStx;
    Term.synthesizeSyntheticMVars false;
    type ← Term.instantiateMVars typeStx type;
    type ← Term.mkForall typeStx xs type;
    (type, _) ← Term.mkForallUsedOnly typeStx vars type;
    type ← Term.levelMVarToParam type;
    let usedParams  := (collectLevelParams {} type).params;
    match sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams with
    | Except.error msg      => Term.throwError stx msg
    | Except.ok levelParams =>
      pure $ Declaration.axiomDecl {
        name     := declName,
        lparams  := levelParams,
        type     := type,
        isUnsafe := modifiers.isUnsafe
      }
    };
  addDecl stx decl;
  applyAttributes stx declName modifiers.attrs AttributeApplicationTime.afterTypeChecking;
  applyAttributes stx declName modifiers.attrs AttributeApplicationTime.afterCompilation

private def checkValidInductiveModifier (ref : Syntax) (modifiers : Modifiers) : CommandElabM Unit := do
when modifiers.isNoncomputable $
  throwError ref "invalid use of 'noncomputable' in inductive declaration";
when modifiers.isPartial $
  throwError ref "invalid use of 'partial' in inductive declaration";
when (modifiers.attrs.size != 0) $
  throwError ref "invalid use of attributes in inductive declaration";
pure ()

private def checkValidCtorModifier (ref : Syntax) (modifiers : Modifiers) : CommandElabM Unit := do
when modifiers.isNoncomputable $
  throwError ref "invalid use of 'noncomputable' in constructor declaration";
when modifiers.isPartial $
  throwError ref "invalid use of 'partial' in constructor declaration";
when modifiers.isUnsafe $
  throwError ref "invalid use of 'unsafe' in constructor declaration";
when (modifiers.attrs.size != 0) $
  throwError ref "invalid use of attributes in constructor declaration";
pure ()

/-
parser! "inductive " >> declId >> optDeclSig >> many ctor
parser! try ("class " >> "inductive ") >> declId >> optDeclSig >> many ctor

Remark: numTokens == 1 for regular `inductive` and 2 for `class inductive`.
-/
private def inductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) (numTokens := 1) : CommandElabM InductiveView := do
checkValidInductiveModifier decl modifiers;
let (binders, type?) := expandOptDeclSig (decl.getArg (numTokens + 1));
let declId           := decl.getArg numTokens;
withDeclId declId fun name => do
  levelNames ← getLevelNames;
  declName   ← mkDeclName declId modifiers name;
  ctors      ← (decl.getArg (numTokens + 2)).getArgs.mapM fun ctor => do {
    -- def ctor := parser! " | " >> declModifiers >> ident >> optional inferMod >> optDeclSig
    ctorModifiers ← elabModifiers (ctor.getArg 1);
    when (ctorModifiers.isPrivate && modifiers.isPrivate) $
      throwError ctor "invalid 'private' constructor in a 'private' inductive datatype";
    when (ctorModifiers.isProtected && modifiers.isPrivate) $
      throwError ctor "invalid 'protected' constructor in a 'private' inductive datatype";
    checkValidCtorModifier ctor ctorModifiers;
    let ctorName := ctor.getIdAt 2;
    let ctorName := declName ++ ctorName;
    ctorName ← applyVisibility (ctor.getArg 2) ctorModifiers.visibility ctorName;
    let inferMod := !(ctor.getArg 3).isNone;
    let (binders, type?) := expandOptDeclSig (ctor.getArg 4);
    pure { ref := ctor, modifiers := ctorModifiers, declName := ctorName, inferMod := inferMod, binders := binders, type? := type? : CtorView }
  };
  pure {
    ref           := decl,
    modifiers     := modifiers,
    shortDeclName := name,
    declName      := declName,
    levelNames    := levelNames,
    binders       := binders,
    type?         := type?,
    ctors         := ctors
  }

private def classInductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM InductiveView :=
inductiveSyntaxToView modifiers decl 2

def elabInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
v ← inductiveSyntaxToView modifiers stx;
elabInductiveCore #[v]

def elabClassInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
v ← classInductiveSyntaxToView modifiers stx;
elabInductiveCore #[v]

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
    throwError stx "unexpected declaration"

/- Return true if all elements of the mutual-block are inductive declarations. -/
private def isMutualInductive (stx : Syntax) : Bool :=
(stx.getArg 1).getArgs.all $ fun elem =>
  let decl     := elem.getArg 1;
  let declKind := decl.getKind;
  declKind == `Lean.Parser.Command.inductive

private def elabMutualInductive (elems : Array Syntax) : CommandElabM Unit := do
views ← elems.mapM $ fun stx => do {
   modifiers ← elabModifiers (stx.getArg 0);
   inductiveSyntaxToView modifiers (stx.getArg 1)
};
elabInductiveCore views

@[builtinCommandElab «mutual»]
def elabMutual : CommandElab :=
fun stx =>
  if isMutualInductive stx then
    elabMutualInductive (stx.getArg 1).getArgs
  else
    throwError stx "not supported"

end Command
end Elab
end Lean
