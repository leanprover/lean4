/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectLevelParams
import Lean.Elab.DeclUtil
import Lean.Elab.DefView
import Lean.Elab.Inductive
import Lean.Elab.Structure
import Lean.Elab.MutualDef
import Lean.Elab.DeclarationRange
namespace Lean.Elab.Command

open Meta

/- Auxiliary function for `expandDeclNamespace?` -/
def expandDeclIdNamespace? (declId : Syntax) : Option (Name × Syntax) :=
  let (id, optUnivDeclStx) := expandDeclIdCore declId
  let scpView := extractMacroScopes id
  match scpView.name with
  | Name.str Name.anonymous s _ => none
  | Name.str pre s _            =>
    let nameNew := { scpView with name := Name.mkSimple s }.review
    if declId.isIdent then
      some (pre, mkIdentFrom declId nameNew)
    else
      some (pre, declId.setArg 0 (mkIdentFrom declId nameNew))
  | _ => none

/- given declarations such as `@[...] def Foo.Bla.f ...` return `some (Foo.Bla, @[...] def f ...)` -/
def expandDeclNamespace? (stx : Syntax) : Option (Name × Syntax) :=
  if !stx.isOfKind `Lean.Parser.Command.declaration then none
  else
    let decl := stx[1]
    let k := decl.getKind
    if k == ``Lean.Parser.Command.abbrev ||
       k == ``Lean.Parser.Command.def ||
       k == ``Lean.Parser.Command.theorem ||
       k == ``Lean.Parser.Command.constant ||
       k == ``Lean.Parser.Command.axiom ||
       k == ``Lean.Parser.Command.inductive ||
       k == ``Lean.Parser.Command.classInductive ||
       k == ``Lean.Parser.Command.structure then
      match expandDeclIdNamespace? decl[1] with
      | some (ns, declId) => some (ns, stx.setArg 1 (decl.setArg 1 declId))
      | none              => none
    else if k == ``Lean.Parser.Command.instance then
      let optDeclId := decl[3]
      if optDeclId.isNone then none
      else match expandDeclIdNamespace? optDeclId[0] with
        | some (ns, declId) => some (ns, stx.setArg 1 (decl.setArg 3 (optDeclId.setArg 0 declId)))
        | none              => none
    else
      none

def elabAxiom (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
  -- leading_parser "axiom " >> declId >> declSig
  let declId             := stx[1]
  let (binders, typeStx) := expandDeclSig stx[2]
  let scopeLevelNames ← getLevelNames
  let ⟨name, declName, allUserLevelNames⟩ ← expandDeclId declId modifiers
  addDeclarationRanges declName stx
  runTermElabM declName fun vars => Term.withLevelNames allUserLevelNames $ Term.elabBinders binders.getArgs fun xs => do
    Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.beforeElaboration
    let type ← Term.elabType typeStx
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let type ← mkForallFVars xs type
    let type ← mkForallFVars vars type (usedOnly := true)
    let (type, _) ← Term.levelMVarToParam type
    let usedParams  := collectLevelParams {} type |>.params
    match sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams with
    | Except.error msg      => throwErrorAt stx msg
    | Except.ok levelParams =>
      let decl := Declaration.axiomDecl {
        name        := declName,
        levelParams := levelParams,
        type        := type,
        isUnsafe    := modifiers.isUnsafe
      }
      Term.ensureNoUnassignedMVars decl
      addDecl decl
      Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.afterTypeChecking
      if isExtern (← getEnv) declName then
        compileDecl decl
      Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.afterCompilation

/-
leading_parser "inductive " >> declId >> optDeclSig >> optional ":=" >> many ctor
leading_parser atomic (group ("class " >> "inductive ")) >> declId >> optDeclSig >> optional ":=" >> many ctor >> optDeriving
-/
private def inductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM InductiveView := do
  checkValidInductiveModifier modifiers
  let (binders, type?) := expandOptDeclSig decl[2]
  let declId           := decl[1]
  let ⟨name, declName, levelNames⟩ ← expandDeclId declId modifiers
  addDeclarationRanges declName decl
  let ctors      ← decl[4].getArgs.mapM fun ctor => withRef ctor do
    -- def ctor := leading_parser " | " >> declModifiers >> ident >> optional inferMod >> optDeclSig
    let ctorModifiers ← elabModifiers ctor[1]
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      throwError "invalid 'private' constructor in a 'private' inductive datatype"
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "invalid 'protected' constructor in a 'private' inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 2
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[2] $ applyVisibility ctorModifiers.visibility ctorName
    let inferMod := !ctor[3].isNone
    let (binders, type?) := expandOptDeclSig ctor[4]
    addDocString' ctorName ctorModifiers.docString?
    addAuxDeclarationRanges ctorName ctor ctor[2]
    pure { ref := ctor, modifiers := ctorModifiers, declName := ctorName, inferMod := inferMod, binders := binders, type? := type? : CtorView }
  let classes ← getOptDerivingClasses decl[5]
  pure {
    ref             := decl
    modifiers       := modifiers
    shortDeclName   := name
    declName        := declName
    levelNames      := levelNames
    binders         := binders
    type?           := type?
    ctors           := ctors
    derivingClasses := classes
  }

private def classInductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM InductiveView :=
  inductiveSyntaxToView modifiers decl

def elabInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
  let v ← inductiveSyntaxToView modifiers stx
  elabInductiveViews #[v]

def elabClassInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
  let modifiers := modifiers.addAttribute { name := `class }
  let v ← classInductiveSyntaxToView modifiers stx
  elabInductiveViews #[v]

@[builtinCommandElab declaration]
def elabDeclaration : CommandElab := fun stx =>
  match expandDeclNamespace? stx with
  | some (ns, newStx) => do
    let ns := mkIdentFrom stx ns
    let newStx ← `(namespace $ns:ident $newStx end $ns:ident)
    withMacroExpansion stx newStx $ elabCommand newStx
  | none => do
    let modifiers ← elabModifiers stx[0]
    let decl     := stx[1]
    let declKind := decl.getKind
    if declKind == ``Lean.Parser.Command.«axiom» then
      elabAxiom modifiers decl
    else if declKind == ``Lean.Parser.Command.«inductive» then
      elabInductive modifiers decl
    else if declKind == ``Lean.Parser.Command.classInductive then
      elabClassInductive modifiers decl
    else if declKind == ``Lean.Parser.Command.«structure» then
      elabStructure modifiers decl
    else if isDefLike decl then
      elabMutualDef #[stx]
    else
      throwError "unexpected declaration"

/- Return true if all elements of the mutual-block are inductive declarations. -/
private def isMutualInductive (stx : Syntax) : Bool :=
  stx[1].getArgs.all fun elem =>
    let decl     := elem[1]
    let declKind := decl.getKind
    declKind == `Lean.Parser.Command.inductive

private def elabMutualInductive (elems : Array Syntax) : CommandElabM Unit := do
  let views ← elems.mapM fun stx => do
     let modifiers ← elabModifiers stx[0]
     inductiveSyntaxToView modifiers stx[1]
  elabInductiveViews views

/- Return true if all elements of the mutual-block are definitions/theorems/abbrevs. -/
private def isMutualDef (stx : Syntax) : Bool :=
  stx[1].getArgs.all fun elem =>
    let decl := elem[1]
    isDefLike decl

private def isMutualPreambleCommand (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``Lean.Parser.Command.variable ||
  k == ``Lean.Parser.Command.universe ||
  k == ``Lean.Parser.Command.check ||
  k == ``Lean.Parser.Command.set_option ||
  k == ``Lean.Parser.Command.open

private partial def splitMutualPreamble (elems : Array Syntax) : Option (Array Syntax × Array Syntax) :=
  let rec loop (i : Nat) : Option (Array Syntax × Array Syntax) :=
    if h : i < elems.size then
      let elem := elems.get ⟨i, h⟩
      if isMutualPreambleCommand elem then
        loop (i+1)
      else if i == 0 then
        none -- `mutual` block does not contain any preamble commands
      else
        some (elems[0:i], elems[i:elems.size])
    else
      none -- a `mutual` block containing only preamble commands is not a valid `mutual` block
  loop 0

@[builtinMacro Lean.Parser.Command.mutual]
def expandMutualNamespace : Macro := fun stx => do
  let mut ns?      := none
  let mut elemsNew := #[]
  for elem in stx[1].getArgs do
    match ns?, expandDeclNamespace? elem with
    | _, none                         => elemsNew := elemsNew.push elem
    | none, some (ns, elem)           => ns? := some ns; elemsNew := elemsNew.push elem
    | some nsCurr, some (nsNew, elem) =>
      if nsCurr == nsNew then
        elemsNew := elemsNew.push elem
      else
        Macro.throwErrorAt elem s!"conflicting namespaces in mutual declaration, using namespace '{nsNew}', but used '{nsCurr}' in previous declaration"
  match ns? with
  | some ns =>
    let ns := mkIdentFrom stx ns
    let stxNew := stx.setArg 1 (mkNullNode elemsNew)
    `(namespace $ns:ident $stxNew end $ns:ident)
  | none => Macro.throwUnsupported

@[builtinMacro Lean.Parser.Command.mutual]
def expandMutualElement : Macro := fun stx => do
  let mut elemsNew := #[]
  let mut modified := false
  for elem in stx[1].getArgs do
    match (← expandMacro? elem) with
    | some elemNew => elemsNew := elemsNew.push elemNew; modified := true
    | none         => elemsNew := elemsNew.push elem
  if modified then
    pure $ stx.setArg 1 (mkNullNode elemsNew)
  else
    Macro.throwUnsupported

@[builtinMacro Lean.Parser.Command.mutual]
def expandMutualPreamble : Macro := fun stx =>
  match splitMutualPreamble stx[1].getArgs with
  | none => Macro.throwUnsupported
  | some (preamble, rest) => do
    let secCmd    ← `(section)
    let newMutual := stx.setArg 1 (mkNullNode rest)
    let endCmd    ← `(end)
    pure $ mkNullNode (#[secCmd] ++ preamble ++ #[newMutual] ++ #[endCmd])

@[builtinCommandElab «mutual»]
def elabMutual : CommandElab := fun stx => do
  if isMutualInductive stx then
    elabMutualInductive stx[1].getArgs
  else if isMutualDef stx then
    elabMutualDef stx[1].getArgs
  else
    throwError "invalid mutual block"

/- leading_parser "attribute " >> "[" >> sepBy1 (eraseAttr <|> Term.attrInstance) ", " >> "]" >> many1 ident -/
@[builtinCommandElab «attribute»] def elabAttr : CommandElab := fun stx => do
  let mut attrInsts := #[]
  let mut toErase := #[]
  for attrKindStx in stx[2].getSepArgs do
    if attrKindStx.getKind == ``Lean.Parser.Command.eraseAttr then
      let attrName := attrKindStx[1].getId.eraseMacroScopes
      unless isAttribute (← getEnv) attrName do
        throwError "unknown attribute [{attrName}]"
      toErase := toErase.push attrName
    else
      attrInsts := attrInsts.push attrKindStx
  let attrs ← elabAttrs attrInsts
  let idents := stx[4].getArgs
  for ident in idents do withRef ident <| liftTermElabM none do
    let declName ← resolveGlobalConstNoOverloadWithInfo ident
    Term.applyAttributes declName attrs
    for attrName in toErase do
      Attribute.erase declName attrName

def expandInitCmd (builtin : Bool) : Macro := fun stx => do
  let optVisibility := stx[0]
  let optHeader     := stx[2]
  let doSeq         := stx[3]
  let attrId        := mkIdentFrom stx $ if builtin then `builtinInit else `init
  if optHeader.isNone then
    unless optVisibility.isNone do
      Macro.throwError "invalid initialization command, 'visibility' modifer is not allowed"
    `(@[$attrId:ident]def initFn : IO Unit := do $doSeq)
  else
    let id   := optHeader[0]
    let type := optHeader[1][1]
    if optVisibility.isNone then
      `(def initFn : IO $type := do $doSeq
        @[$attrId:ident initFn] constant $id : $type)
    else if optVisibility[0].getKind == ``Parser.Command.private then
      `(def initFn : IO $type := do $doSeq
        @[$attrId:ident initFn] private constant $id : $type)
    else if optVisibility[0].getKind == ``Parser.Command.protected then
      `(def initFn : IO $type := do $doSeq
        @[$attrId:ident initFn] protected constant $id : $type)
    else
      Macro.throwError "unexpected visibility annotation"

@[builtinMacro Lean.Parser.Command.«initialize»] def expandInitialize : Macro :=
  expandInitCmd (builtin := false)

@[builtinMacro Lean.Parser.Command.«builtin_initialize»] def expandBuiltinInitialize : Macro :=
  expandInitCmd (builtin := true)

end Lean.Elab.Command
