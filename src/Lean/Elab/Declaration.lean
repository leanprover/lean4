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
import Lean.Elab.MutualDef

namespace Lean
namespace Elab
namespace Command

open Meta

/- Auxiliary function for `expandDeclNamespace?` -/
def expandDeclIdNamespace? (declId : Syntax) : Option (Name × Syntax) :=
let (id, optUnivDeclStx) := expandDeclIdCore declId;
let scpView := extractMacroScopes id;
match scpView.name with
| Name.str Name.anonymous s _ => none
| Name.str pre s _            =>
  let nameNew := { scpView with name := mkNameSimple s }.review;
  if declId.isIdent then
    some (pre, mkIdentFrom declId nameNew)
  else
    some (pre, declId.setArg 0 (mkIdentFrom declId nameNew))
| _ => none

/- given declarations such as `@[...] def Foo.Bla.f ...` return `some (Foo.Bla, @[...] def f ...)` -/
def expandDeclNamespace? (stx : Syntax) : Option (Name × Syntax) :=
if !stx.isOfKind `Lean.Parser.Command.declaration then none
else
  let decl := stx.getArg 1;
  let k := decl.getKind;
  if k == `Lean.Parser.Command.abbrev ||
     k == `Lean.Parser.Command.def ||
     k == `Lean.Parser.Command.theorem ||
     k == `Lean.Parser.Command.constant ||
     k == `Lean.Parser.Command.axiom ||
     k == `Lean.Parser.Command.inductive ||
     k == `Lean.Parser.Command.structure then
    match expandDeclIdNamespace? (decl.getArg 1) with
    | some (ns, declId) => some (ns, stx.setArg 1 (decl.setArg 1 declId))
    | none              => none
  else if k == `Lean.Parser.Command.instance then
    let optDeclId := decl.getArg 1;
    if optDeclId.isNone then none
    else match expandDeclIdNamespace? (optDeclId.getArg 0) with
      | some (ns, declId) => some (ns, stx.setArg 1 (decl.setArg 1 (optDeclId.setArg 0 declId)))
      | none              => none
  else if k == `Lean.Parser.Command.classInductive then
    match expandDeclIdNamespace? (decl.getArg 2) with
    | some (ns, declId) => some (ns, stx.setArg 1 (decl.setArg 2 declId))
    | none              => none
  else
    none

def elabAxiom (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
-- parser! "axiom " >> declId >> declSig
let declId             := stx.getArg 1;
let (binders, typeStx) := expandDeclSig (stx.getArg 2);
scopeLevelNames ← getLevelNames;
⟨name, declName, allUserLevelNames⟩ ← expandDeclId declId modifiers;
runTermElabM declName $ fun vars => Term.withLevelNames allUserLevelNames $ Term.elabBinders binders.getArgs fun xs => do
  applyAttributes declName modifiers.attrs AttributeApplicationTime.beforeElaboration;
  type ← Term.elabType typeStx;
  Term.synthesizeSyntheticMVarsNoPostponing;
  type ← instantiateMVars type;
  type ← mkForallFVars xs type;
  (type, _) ← mkForallUsedOnly vars type;
  (type, _) ← Term.levelMVarToParam type;
  let usedParams  := (collectLevelParams {} type).params;
  match sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams with
  | Except.error msg      => throwErrorAt stx msg
  | Except.ok levelParams => do
    let decl := Declaration.axiomDecl {
      name     := declName,
      lparams  := levelParams,
      type     := type,
      isUnsafe := modifiers.isUnsafe
    };
    Term.ensureNoUnassignedMVars decl;
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
⟨name, declName, levelNames⟩ ← expandDeclId declId modifiers;
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
fun stx => match expandDeclNamespace? stx with
| some (ns, newStx) => do
  let ns := mkIdentFrom stx ns;
  newStx ← `(namespace $ns:ident $newStx end $ns:ident);
  withMacroExpansion stx newStx $ elabCommand newStx
| none => do
  modifiers ← elabModifiers (stx.getArg 0);
  let decl     := stx.getArg 1;
  let declKind := decl.getKind;
  if declKind == `Lean.Parser.Command.axiom then
    elabAxiom modifiers decl
  else if declKind == `Lean.Parser.Command.inductive then
    elabInductive modifiers decl
  else if declKind == `Lean.Parser.Command.classInductive then
    elabClassInductive modifiers decl
  else if declKind == `Lean.Parser.Command.structure then
    elabStructure modifiers decl
  else if isDefLike decl then do
    elabMutualDef #[stx]
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

/- Return true if all elements of the mutual-block are definitions/theorems/abbrevs. -/
private def isMutualDef (stx : Syntax) : Bool :=
(stx.getArg 1).getArgs.all $ fun elem =>
  let decl := elem.getArg 1;
  isDefLike decl

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
  let newMutual := stx.setArg 1 (mkNullNode rest);
  endCmd    ← `(end);
  pure (some (mkNullNode (#[secCmd] ++ preamble ++ #[newMutual] ++ #[endCmd])))
| none =>
  pure none

private def expandMutualElement? (stx : Syntax) : CommandElabM (Option Syntax) := do
env ← getEnv;
let elems := (stx.getArg 1).getArgs;
(elemsNew, modified) ← elems.foldlM
  (fun (acc : Array Syntax × Bool) elem => do
     let (elemsNew, modified) := acc;
     elem? ← liftMacroM $ expandMacro? env elem;
     match elem? with
     | some elemNew => pure (elemsNew.push elemNew, true)
     | none         => pure (elemsNew.push elem, modified))
  (#[], false);
if modified then
  pure (some (stx.setArg 1 (mkNullNode elemsNew)))
else
  pure none

private def expandMutualNamespace? (stx : Syntax) : MacroM (Option Syntax) := do
let elems := (stx.getArg 1).getArgs;
(ns?, elems) ← elems.foldlM
  (fun (acc : Option Name × Array Syntax) (elem : Syntax) =>
    let (ns?, elems) := acc;
    match ns?, expandDeclNamespace? elem with
    | _, none                         => pure (ns?, elems.push elem)
    | none, some (ns, elem)           => pure (some ns, elems.push elem)
    | some nsCurr, some (nsNew, elem) =>
      if nsCurr == nsNew then
        pure (ns?, elems.push elem)
      else
        Macro.throwError elem
          ("conflicting namespaces in mutual declaration, using namespace '" ++ toString nsNew ++ "', but used '" ++ toString nsCurr ++ "' in previous declaration"))
  (none, #[]);
match ns? with
| none    => pure none
| some ns =>
  let ns := mkIdentFrom stx ns;
  let stxNew := stx.setArg 1 (mkNullNode elems);
  `(namespace $ns:ident $stxNew end $ns:ident)

@[builtinCommandElab «mutual»]
def elabMutual : CommandElab :=
fun stx => do
  stxNew? ← liftMacroM $ expandMutualPreamble? stx;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabCommand stxNew
  | none        => do
  stxNew? ← expandMutualElement? stx;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabCommand stxNew
  | none => do
  stxNew? ← liftMacroM $ expandMutualNamespace? stx;
  match stxNew? with
  | some stxNew => withMacroExpansion stx stxNew $ elabCommand stxNew
  | none =>
  if isMutualInductive stx then
    elabMutualInductive (stx.getArg 1).getArgs
  else if isMutualDef stx then
    elabMutualDef (stx.getArg 1).getArgs
  else
    throwError "invalid mutual block"

end Command
end Elab
end Lean
