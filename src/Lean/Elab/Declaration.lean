/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
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

private def setDeclIdName (declId : Syntax) (nameNew : Name) : Syntax :=
  let (id, _) := expandDeclIdCore declId
  -- We should not update the name of `def _root_.` declarations
  assert! !(`_root_).isPrefixOf id
  let idStx := mkIdent nameNew |>.raw.setInfo declId.getHeadInfo
  if declId.isIdent then
    idStx
  else
    declId.setArg 0 idStx

/-- Return `true` if `stx` is a `Command.declaration`, and it is a definition that always has a name. -/
private def isNamedDef (stx : Syntax) : Bool :=
  if !stx.isOfKind ``Lean.Parser.Command.declaration then
    false
  else
    let decl := stx[1]
    let k := decl.getKind
    k == ``Lean.Parser.Command.abbrev ||
    k == ``Lean.Parser.Command.definition ||
    k == ``Lean.Parser.Command.theorem ||
    k == ``Lean.Parser.Command.opaque ||
    k == ``Lean.Parser.Command.axiom ||
    k == ``Lean.Parser.Command.inductive ||
    k == ``Lean.Parser.Command.classInductive ||
    k == ``Lean.Parser.Command.structure

/-- Return `true` if `stx` is an `instance` declaration command -/
private def isInstanceDef (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Command.declaration &&
  stx[1].getKind == ``Lean.Parser.Command.instance

/-- Return `some name` if `stx` is a definition named `name` -/
private def getDefName? (stx : Syntax) : Option Name := do
  if isNamedDef stx then
    let (id, _) := expandDeclIdCore stx[1][1]
    some id
  else if isInstanceDef stx then
    let optDeclId := stx[1][3]
    if optDeclId.isNone then none
    else
      let (id, _) := expandDeclIdCore optDeclId[0]
      some id
  else
    none

/--
Update the name of the given definition.
This function assumes `stx` is not a nameless instance.
-/
private def setDefName (stx : Syntax) (name : Name) : Syntax :=
  if isNamedDef stx then
    stx.setArg 1 <| stx[1].setArg 1 <| setDeclIdName stx[1][1] name
  else if isInstanceDef stx then
    -- We never set the name of nameless instance declarations
    assert! !stx[1][3].isNone
    stx.setArg 1 <| stx[1].setArg 3 <| stx[1][3].setArg 0 <| setDeclIdName stx[1][3][0] name
  else
    stx

/--
  Given declarations such as `@[...] def Foo.Bla.f ...` return `some (Foo.Bla, @[...] def f ...)`
  Remark: if the id starts with `_root_`, we return `none`.
-/
private def expandDeclNamespace? (stx : Syntax) : MacroM (Option (Name × Syntax)) := do
  let some name := getDefName? stx | return none
  if (`_root_).isPrefixOf name then
    ensureValidNamespace (name.replacePrefix `_root_ Name.anonymous)
    return none
  let scpView := extractMacroScopes name
  match scpView.name with
  | .str .anonymous _ => return none
  | .str pre shortName => return some (pre, setDefName stx { scpView with name := .mkSimple shortName }.review)
  | _ => return none

def elabAxiom (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
  -- leading_parser "axiom " >> declId >> declSig
  let declId             := stx[1]
  let (binders, typeStx) := expandDeclSig stx[2]
  runTermElabM fun vars => do
    let scopeLevelNames ← Term.getLevelNames
    let ⟨shortName, declName, allUserLevelNames⟩ ← Term.expandDeclId (← getCurrNamespace) scopeLevelNames declId modifiers
    addDeclarationRangesForBuiltin declName modifiers.stx stx
    Term.withAutoBoundImplicitForbiddenPred (fun n => shortName == n) do
    Term.withDeclName declName <| Term.withLevelNames allUserLevelNames <| Term.elabBinders binders.getArgs fun xs => do
      Term.applyAttributesAt declName modifiers.attrs AttributeApplicationTime.beforeElaboration
      let type ← Term.elabType typeStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let xs ← Term.addAutoBoundImplicits xs
      let type ← instantiateMVars type
      let type ← mkForallFVars xs type
      let type ← mkForallFVars vars type (usedOnly := true)
      let type ← Term.levelMVarToParam type
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

/--
Macro that expands a declaration with a complex name into an explicit `namespace` block.
Implementing this step as a macro means that reuse checking is handled by `elabCommand`.
 -/
@[builtin_macro Lean.Parser.Command.declaration]
def expandNamespacedDeclaration : Macro := fun stx => do
  match (← expandDeclNamespace? stx) with
  | some (ns, newStx) => do
    -- Limit ref variability for incrementality; see Note [Incremental Macros]
    let declTk := stx[1][0]
    let ns := mkIdentFrom declTk ns
    withRef declTk `(namespace $ns $(⟨newStx⟩) end $ns)
  | none => Macro.throwUnsupported

@[builtin_command_elab declaration, builtin_incremental]
def elabDeclaration : CommandElab := fun stx => do
  let decl     := stx[1]
  let declKind := decl.getKind
  if isDefLike decl then
    -- only case implementing incrementality currently
    elabMutualDef #[stx]
  else withoutCommandIncrementality true do
    let modifiers : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
    if declKind == ``Lean.Parser.Command.«axiom» then
      let modifiers ← elabModifiers modifiers
      elabAxiom modifiers decl
    else if declKind == ``Lean.Parser.Command.«inductive» then
      let modifiers ← elabModifiers modifiers
      elabInductive modifiers decl
    else if declKind == ``Lean.Parser.Command.classInductive then
      let modifiers ← elabModifiers modifiers
      elabClassInductive modifiers decl
    else if declKind == ``Lean.Parser.Command.«structure» then
      let modifiers ← elabModifiers modifiers
      elabStructure modifiers decl
    else
      throwError "unexpected declaration"

/-- Return true if all elements of the mutual-block are definitions/theorems/abbrevs. -/
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
      if isMutualPreambleCommand elems[i] then
        loop (i+1)
      else if i == 0 then
        none -- `mutual` block does not contain any preamble commands
      else
        some (elems[0:i], elems[i:elems.size])
    else
      none -- a `mutual` block containing only preamble commands is not a valid `mutual` block
  loop 0

/--
Find the common namespace for the given names.
Example:
```
findCommonPrefix [`Lean.Elab.eval, `Lean.mkConst, `Lean.Elab.Tactic.evalTactic]
-- `Lean
```
-/
def findCommonPrefix (ns : List Name) : Name :=
  match ns with
  | [] => .anonymous
  | n :: ns => go n ns
where
  go (n : Name) (ns : List Name) : Name :=
    match n with
    | .anonymous => .anonymous
    | _ => match ns with
      | [] => n
      | n' :: ns => go (findCommon n.components n'.components) ns
  findCommon (as bs : List Name) : Name :=
    match as, bs with
    | a :: as, b :: bs => if a == b then a ++ findCommon as bs else .anonymous
    | _, _ => .anonymous


@[builtin_macro Lean.Parser.Command.mutual]
def expandMutualNamespace : Macro := fun stx => do
  let mut nss := #[]
  for elem in stx[1].getArgs do
    match (← expandDeclNamespace? elem) with
    | none        => Macro.throwUnsupported
    | some (n, _) => nss := nss.push n
  let common := findCommonPrefix nss.toList
  if common.isAnonymous then Macro.throwUnsupported
  let elemsNew ← stx[1].getArgs.mapM fun elem => do
    let some name := getDefName? elem | unreachable!
    let view := extractMacroScopes name
    let nameNew := { view with name := view.name.replacePrefix common .anonymous }.review
    return setDefName elem nameNew
  let ns := mkIdentFrom stx common
  let stxNew := stx.setArg 1 (mkNullNode elemsNew)
  `(namespace $ns $(⟨stxNew⟩) end $ns)

@[builtin_macro Lean.Parser.Command.mutual]
def expandMutualElement : Macro := fun stx => do
  let mut elemsNew := #[]
  let mut modified := false
  for elem in stx[1].getArgs do
    -- Don't trigger the `expandNamespacedDecl` macro, the namespace is handled by the mutual def
    -- elaborator directly instead
    if elem.isOfKind ``Parser.Command.declaration then
      continue
    match (← expandMacro? elem) with
    | some elemNew => elemsNew := elemsNew.push elemNew; modified := true
    | none         => elemsNew := elemsNew.push elem
  if modified then
    return stx.setArg 1 (mkNullNode elemsNew)
  else
    Macro.throwUnsupported

@[builtin_macro Lean.Parser.Command.mutual]
def expandMutualPreamble : Macro := fun stx =>
  match splitMutualPreamble stx[1].getArgs with
  | none => Macro.throwUnsupported
  | some (preamble, rest) => do
    let secCmd    ← `(section)
    let newMutual := stx.setArg 1 (mkNullNode rest)
    let endCmd    ← `(end)
    return mkNullNode (#[secCmd] ++ preamble ++ #[newMutual] ++ #[endCmd])

@[builtin_command_elab «mutual», builtin_incremental]
def elabMutual : CommandElab := fun stx => do
  if isMutualDef stx then
    -- only case implementing incrementality currently
    elabMutualDef stx[1].getArgs
  else withoutCommandIncrementality true do
    if isMutualInductive stx then
      elabMutualInductive stx[1].getArgs
    else
      throwError "invalid mutual block: either all elements of the block must be inductive declarations, or they must all be definitions/theorems/abbrevs"

/- leading_parser "attribute " >> "[" >> sepBy1 (eraseAttr <|> Term.attrInstance) ", " >> "]" >> many1 ident -/
@[builtin_command_elab «attribute»] def elabAttr : CommandElab := fun stx => do
  let mut attrInsts := #[]
  let mut toErase := #[]
  for attrKindStx in stx[2].getSepArgs do
    if attrKindStx.getKind == ``Lean.Parser.Command.eraseAttr then
      let attrName := attrKindStx[1].getId.eraseMacroScopes
      if isAttribute (← getEnv) attrName then
        toErase := toErase.push attrName
      else
        logErrorAt attrKindStx m!"unknown attribute [{attrName}]"
    else
      attrInsts := attrInsts.push attrKindStx
  let attrs ← elabAttrs attrInsts
  let idents := stx[4].getArgs
  for ident in idents do withRef ident <| liftTermElabM do
    /-
    HACK to allow `attribute` command to disable builtin simprocs.
    TODO: find a better solution. Example: have some "fake" declaration
    for builtin simprocs.
    -/
    let declNames ←
      try
        realizeGlobalConstWithInfos ident
      catch _ =>
        let name := ident.getId.eraseMacroScopes
        if (← Simp.isBuiltinSimproc name) then
          pure [name]
        else
          throwUnknownConstant name
    let declName ← ensureNonAmbiguous ident declNames
    Term.applyAttributes declName attrs
    for attrName in toErase do
      Attribute.erase declName attrName

@[builtin_command_elab Lean.Parser.Command.«initialize»] def elabInitialize : CommandElab
  | stx@`($declModifiers:declModifiers $kw:initializeKeyword $[$id? : $type? ←]? $doSeq) => do
    let attrId := mkIdentFrom stx <| if kw.raw[0].isToken "initialize" then `init else `builtin_init
    if let (some id, some type) := (id?, type?) then
      let `(Parser.Command.declModifiersT| $[$doc?:docComment]? $[@[$attrs?,*]]? $(vis?)? $[unsafe%$unsafe?]?) := stx[0]
        | throwErrorAt declModifiers "invalid initialization command, unexpected modifiers"
      let defStx ← `($[$doc?:docComment]? @[$attrId:ident initFn, $(attrs?.getD ∅),*] $(vis?)? opaque $id : $type)
      let mut fullId := (← getCurrNamespace) ++ id.getId
      if vis?.any (·.raw.isOfKind ``Parser.Command.private) then
        fullId := mkPrivateName (← getEnv) fullId
      -- We need to add `id`'s ranges *before* elaborating `initFn` (and then `id` itself) as
      -- otherwise the info context created by `with_decl_name` will be incomplete and break the
      -- call hierarchy
      addDeclarationRangesForBuiltin fullId ⟨defStx.raw[0]⟩ defStx.raw[1]
      elabCommand (← `(
        $[unsafe%$unsafe?]? def initFn : IO $type := with_decl_name% $(mkIdent fullId) do $doSeq
        $defStx:command))
    else
      let `(Parser.Command.declModifiersT| $[$doc?:docComment]? ) := declModifiers
        | throwErrorAt declModifiers "invalid initialization command, unexpected modifiers"
      elabCommand (← `($[$doc?:docComment]? @[$attrId:ident] def initFn : IO Unit := do $doSeq))
  | _ => throwUnsupportedSyntax

builtin_initialize
  registerTraceClass `Elab.axiom

end Lean.Elab.Command
