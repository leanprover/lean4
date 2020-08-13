/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectLevelParams
import Lean.Elab.DeclUtil
import Lean.Elab.Definition
import Lean.Elab.Inductive
import Lean.Elab.Structure

namespace Lean
namespace Elab
namespace Command

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
  | none        => throwError "not implemented yet";
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
  declName          ← mkDeclName modifiers name;
  applyAttributes declName modifiers.attrs AttributeApplicationTime.beforeElaboration;
  allUserLevelNames ← getLevelNames;
  decl ← runTermElabM declName $ fun vars => Term.elabBinders binders.getArgs $ fun xs => do {
    type ← Term.elabType typeStx;
    Term.synthesizeSyntheticMVars false;
    type ← Term.instantiateMVars type;
    type ← Term.mkForall xs type;
    (type, _) ← Term.mkForallUsedOnly vars type;
    (type, _) ← Term.levelMVarToParam type;
    let usedParams  := (collectLevelParams {} type).params;
    match sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams with
    | Except.error msg      => Term.throwErrorAt stx msg
    | Except.ok levelParams =>
      pure $ Declaration.axiomDecl {
        name     := declName,
        lparams  := levelParams,
        type     := type,
        isUnsafe := modifiers.isUnsafe
      }
    };
  addDecl decl;
  applyAttributes declName modifiers.attrs AttributeApplicationTime.afterTypeChecking;
  applyAttributes declName modifiers.attrs AttributeApplicationTime.afterCompilation

/-
parser! "inductive " >> declId >> optDeclSig >> many ctor
parser! try ("class " >> "inductive ") >> declId >> optDeclSig >> many ctor

Remark: numTokens == 1 for regular `inductive` and 2 for `class inductive`.
-/
private def inductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) (numTokens := 1) : CommandElabM InductiveView := do
checkValidInductiveModifier modifiers;
let (binders, type?) := expandOptDeclSig (decl.getArg (numTokens + 1));
let declId           := decl.getArg numTokens;
withDeclId declId fun name => do
  levelNames ← getLevelNames;
  declName   ← mkDeclName modifiers name;
  ctors      ← (decl.getArg (numTokens + 2)).getArgs.mapM fun ctor => withRef ctor do {
    -- def ctor := parser! " | " >> declModifiers >> ident >> optional inferMod >> optDeclSig
    ctorModifiers ← elabModifiers (ctor.getArg 1);
    when (ctorModifiers.isPrivate && modifiers.isPrivate) $
      throwError "invalid 'private' constructor in a 'private' inductive datatype";
    when (ctorModifiers.isProtected && modifiers.isPrivate) $
      throwError "invalid 'protected' constructor in a 'private' inductive datatype";
    checkValidCtorModifier ctorModifiers;
    let ctorName := ctor.getIdAt 2;
    let ctorName := declName ++ ctorName;
    ctorName ← withRef (ctor.getArg 2) $ applyVisibility ctorModifiers.visibility ctorName;
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
elabInductiveViews #[v]

def elabClassInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
let modifiers := modifiers.addAttribute { name := `class };
v ← classInductiveSyntaxToView modifiers stx;
elabInductiveViews #[v]

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
    throwError "unexpected declaration"

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
elabInductiveViews views

private def isMutualPreambleCommand (stx : Syntax) : Bool :=
let k := stx.getKind;
k == `Lean.Parser.Command.variable ||
k == `Lean.Parser.Command.variables ||
k == `Lean.Parser.Command.universe ||
k == `Lean.Parser.Command.universes ||
k == `Lean.Parser.Command.check ||
k == `Lean.Parser.Command.set_option ||
k == `Lean.Parser.Command.open

private partial def splitMutualPreamble (elems : Array Syntax) : Nat → Option (Array Syntax × Array Syntax)
| i =>
  if h : i < elems.size then
    let elem := elems.get ⟨i, h⟩;
    if isMutualPreambleCommand elem then
      splitMutualPreamble (i+1)
    else if i == 0 then
      none -- `mutual` block does not contain any preamble commands
    else
      some (elems.extract 0 i, elems.extract i elems.size)
  else
    none -- a `mutual` block containing only preamble commands is not a valid `mutual` block

private def expandMutualPreamble? (stx : Syntax) : MacroM (Option Syntax) :=
match splitMutualPreamble (stx.getArg 1).getArgs 0 with
| some (preamble, rest) => do
  secCmd    ← `(section);
  newMutual ← `(mutual $rest* end);
  endCmd    ← `(end);
  pure (some (mkNullNode (#[secCmd] ++ preamble ++ #[newMutual] ++ #[endCmd])))
| none =>
  pure none

@[builtinCommandElab «mutual»]
def elabMutual : CommandElab :=
fun stx => do
  stxNew? ← liftMacroM $ expandMutualPreamble? stx;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabCommand stxNew
  | none        =>
    if isMutualInductive stx then
      elabMutualInductive (stx.getArg 1).getArgs
    else
      throwError "invalid mutual block"

end Command
end Elab
end Lean
