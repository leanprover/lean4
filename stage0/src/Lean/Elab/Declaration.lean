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

private def ensureValidNamespace (name : Name) : MacroM Unit := do
  match name with
  | .str p s =>
    if s == "_root_" then
      Macro.throwError s!"invalid namespace '{name}', '_root_' is a reserved namespace"
    ensureValidNamespace p
  | .num .. => Macro.throwError s!"invalid namespace '{name}', it must not contain numeric parts"
  | .anonymous => return ()

/-- Auxiliary function for `expandDeclNamespace?` -/
private def expandDeclIdNamespace? (declId : Syntax) : MacroM (Option (Name × Syntax)) := do
  let (id, _) := expandDeclIdCore declId
  if (`_root_).isPrefixOf id then
    ensureValidNamespace (id.replacePrefix `_root_ Name.anonymous)
    return none
  let scpView := extractMacroScopes id
  match scpView.name with
  | .str .anonymous _ => return none
  | .str pre s        =>
    ensureValidNamespace pre
    let nameNew := { scpView with name := Name.mkSimple s }.review
    -- preserve "original" info, if any, so that hover etc. on the namespaced
    -- name access the info tree node of the declaration name
    let id := mkIdent nameNew |>.raw.setInfo declId.getHeadInfo
    if declId.isIdent then
      return some (pre, id)
    else
      return some (pre, declId.setArg 0 id)
  | _ => return none

/--
  Given declarations such as `@[...] def Foo.Bla.f ...` return `some (Foo.Bla, @[...] def f ...)`
  Remark: if the id starts with `_root_`, we return `none`.
-/
private def expandDeclNamespace? (stx : Syntax) : MacroM (Option (Name × Syntax)) := do
  if !stx.isOfKind `Lean.Parser.Command.declaration then
    return none
  else
    let decl := stx[1]
    let k := decl.getKind
    if k == ``Lean.Parser.Command.abbrev ||
       k == ``Lean.Parser.Command.def ||
       k == ``Lean.Parser.Command.theorem ||
       k == ``Lean.Parser.Command.opaque ||
       k == ``Lean.Parser.Command.axiom ||
       k == ``Lean.Parser.Command.inductive ||
       k == ``Lean.Parser.Command.classInductive ||
       k == ``Lean.Parser.Command.structure then
      match (← expandDeclIdNamespace? decl[1]) with
      | some (ns, declId) => return some (ns, stx.setArg 1 (decl.setArg 1 declId))
      | none              => return none
    else if k == ``Lean.Parser.Command.instance then
      let optDeclId := decl[3]
      if optDeclId.isNone then return none
      else match (← expandDeclIdNamespace? optDeclId[0]) with
        | some (ns, declId) => return some (ns, stx.setArg 1 (decl.setArg 3 (optDeclId.setArg 0 declId)))
        | none              => return none
    else
      return none

def elabAxiom (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
  -- leading_parser "axiom " >> declId >> declSig
  let declId             := stx[1]
  let (binders, typeStx) := expandDeclSig stx[2]
  let scopeLevelNames ← getLevelNames
  let ⟨_, declName, allUserLevelNames⟩ ← expandDeclId declId modifiers
  addDeclarationRanges declName stx
  runTermElabM declName fun vars => Term.withLevelNames allUserLevelNames <| Term.elabBinders binders.getArgs fun xs => do
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
      let type ← instantiateMVars type
      let decl := Declaration.axiomDecl {
        name        := declName,
        levelParams := levelParams,
        type        := type,
        isUnsafe    := modifiers.isUnsafe
      }
      trace[Elab.axiom] "{declName} : {type}"
      Term.ensureNoUnassignedMVars decl
      addDecl decl
      withSaveInfoContext do  -- save new env
        Term.addTermInfo' declId (← mkConstWithLevelParams declName) (isBinder := true)
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
    -- def ctor := leading_parser " | " >> declModifiers >> ident >> optDeclSig
    let ctorModifiers ← elabModifiers ctor[1]
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      throwError "invalid 'private' constructor in a 'private' inductive datatype"
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "invalid 'protected' constructor in a 'private' inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 2
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[2] <| applyVisibility ctorModifiers.visibility ctorName
    let (binders, type?) := expandOptDeclSig ctor[3]
    addDocString' ctorName ctorModifiers.docString?
    addAuxDeclarationRanges ctorName ctor ctor[2]
    return { ref := ctor, modifiers := ctorModifiers, declName := ctorName, binders := binders, type? := type? : CtorView }
  let mut computedFields := #[]
  let mut classes := #[]
  if decl.getNumArgs == 6 then
    -- TODO: remove after stage0 update
    classes ← getOptDerivingClasses decl[5]
  else
    computedFields ← (decl[5].getOptional?.map (·[1].getArgs) |>.getD #[]).mapM fun cf => withRef cf do
      return { ref := cf, modifiers := cf[0], fieldId := cf[1].getId, type := ⟨cf[3]⟩, matchAlts := ⟨cf[4]⟩ }
    classes ← getOptDerivingClasses decl[6]
  return {
    ref             := decl
    shortDeclName   := name
    derivingClasses := classes
    declId, modifiers, declName, levelNames
    binders, type?, ctors
    computedFields
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

def getTerminationHints (stx : Syntax) : TerminationHints :=
  let decl := stx[1]
  let k := decl.getKind
  if k == ``Parser.Command.def || k == ``Parser.Command.theorem || k == ``Parser.Command.instance then
    let args := decl.getArgs
    { terminationBy? := args[args.size - 2]!.getOptional?, decreasingBy? := args[args.size - 1]!.getOptional? }
  else
    {}

@[builtinCommandElab declaration]
def elabDeclaration : CommandElab := fun stx => do
  match (← liftMacroM <| expandDeclNamespace? stx) with
  | some (ns, newStx) => do
    let ns := mkIdentFrom stx ns
    let newStx ← `(namespace $ns:ident $(⟨newStx⟩) end $ns:ident)
    withMacroExpansion stx newStx <| elabCommand newStx
  | none => do
    let decl     := stx[1]
    let declKind := decl.getKind
    if declKind == ``Lean.Parser.Command.«axiom» then
      let modifiers ← elabModifiers stx[0]
      elabAxiom modifiers decl
    else if declKind == ``Lean.Parser.Command.«inductive» then
      let modifiers ← elabModifiers stx[0]
      elabInductive modifiers decl
    else if declKind == ``Lean.Parser.Command.classInductive then
      let modifiers ← elabModifiers stx[0]
      elabClassInductive modifiers decl
    else if declKind == ``Lean.Parser.Command.«structure» then
      let modifiers ← elabModifiers stx[0]
      elabStructure modifiers decl
    else if isDefLike decl then
      elabMutualDef #[stx] (getTerminationHints stx)
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
    match ns?, (← expandDeclNamespace? elem) with
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
    `(namespace $ns:ident $(⟨stxNew⟩) end $ns:ident)
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
    return stx.setArg 1 (mkNullNode elemsNew)
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
    return mkNullNode (#[secCmd] ++ preamble ++ #[newMutual] ++ #[endCmd])

@[builtinCommandElab «mutual»]
def elabMutual : CommandElab := fun stx => do
  let hints := { terminationBy? := stx[3].getOptional?, decreasingBy? := stx[4].getOptional? }
  if isMutualInductive stx then
    if let some bad := hints.terminationBy? then
      throwErrorAt bad "invalid 'termination_by' in mutually inductive datatype declaration"
    if let some bad := hints.decreasingBy? then
      throwErrorAt bad "invalid 'decreasing_by' in mutually inductive datatype declaration"
    elabMutualInductive stx[1].getArgs
  else if isMutualDef stx then
    for arg in stx[1].getArgs do
      let argHints := getTerminationHints arg
      if let some bad := argHints.terminationBy? then
        throwErrorAt bad "invalid 'termination_by' in 'mutual' block, it must be used after the 'end' keyword"
      if let some bad := argHints.decreasingBy? then
        throwErrorAt bad "invalid 'decreasing_by' in 'mutual' block, it must be used after the 'end' keyword"
    elabMutualDef stx[1].getArgs hints
  else
    throwError "invalid mutual block"

/- leading_parser "attribute " >> "[" >> sepBy1 (eraseAttr <|> Term.attrInstance) ", " >> "]" >> many1 ident -/
@[builtinCommandElab «attribute»] def elabAttr : CommandElab := fun stx => do
  let mut attrInsts := #[]
  let mut toErase := #[]
  for attrKindStx in stx[2].getSepArgs do
    if attrKindStx.getKind == ``Lean.Parser.Command.eraseAttr then
      let attrName := attrKindStx[1].getId.eraseMacroScopes
      if isAttribute (← getEnv) attrName then
        toErase := toErase.push attrName
      else
        logErrorAt attrKindStx "unknown attribute [{attrName}]"
    else
      attrInsts := attrInsts.push attrKindStx
  let attrs ← elabAttrs attrInsts
  let idents := stx[4].getArgs
  for ident in idents do withRef ident <| liftTermElabM none do
    let declName ← resolveGlobalConstNoOverloadWithInfo ident
    Term.applyAttributes declName attrs
    for attrName in toErase do
      Attribute.erase declName attrName

@[builtinMacro Lean.Parser.Command.«initialize»] def expandInitialize : Macro
  | stx@`($declModifiers:declModifiers $kw:initializeKeyword $[$id? : $type? ←]? $doSeq) => do
    let attrId := mkIdentFrom stx <| if kw.raw[0].isToken "initialize" then `init else `builtinInit
    if let (some id, some type) := (id?, type?) then
      let `(Parser.Command.declModifiersT| $[$doc?:docComment]? $[@[$attrs?,*]]? $(vis?)? $[unsafe%$unsafe?]?) := stx[0]
        | Macro.throwErrorAt declModifiers "invalid initialization command, unexpected modifiers"
      let declModifiers ← `(Parser.Command.declModifiersT| $[$doc?:docComment]? @[$attrId:ident initFn, $(attrs?.getD ∅),*] $(vis?)? $[unsafe%$unsafe?]?)
      `(def initFn : IO $type := do $doSeq
        $(⟨declModifiers⟩):declModifiers opaque $id : $type)
    else
      if let `(Parser.Command.declModifiersT| ) := declModifiers then
        `(@[$attrId:ident] def initFn : IO Unit := do $doSeq)
      else
        Macro.throwErrorAt declModifiers "invalid initialization command, unexpected modifiers"
  | _ => Macro.throwUnsupported

builtin_initialize
  registerTraceClass `Elab.axiom

end Lean.Elab.Command
