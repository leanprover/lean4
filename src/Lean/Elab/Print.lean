/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Eqns
public import Lean.Elab.Command
import Lean.PrettyPrinter.Delaborator.Builtins
public section
namespace Lean.Elab.Command

private def throwUnknownId (id : Name) : CommandElabM Unit :=
  throwError "Unknown identifier `{.ofConstName id}`"

private def levelParamsToMessageData (levelParams : List Name) : MessageData :=
  match levelParams with
  | []    => ""
  | u::us => Id.run do
    let mut m := m!".\{{u}"
    for u in us do
      m := m ++ ", " ++ toMessageData u
    return m ++ "}"

private def mkHeader (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (safety : DefinitionSafety) (sig : Bool := true) : CommandElabM MessageData := do
  let mut attrs := #[]
  match (← getReducibilityStatus id) with
  | .irreducible =>   attrs := attrs.push m!"irreducible"
  | .reducible =>     attrs := attrs.push m!"reducible"
  | .instanceReducible => attrs := attrs.push m!"instance_reducible"
  | .semireducible => pure ()

  let env ← getEnv
  if env.header.isModule && (env.setExporting true |>.find? id |>.any (·.isDefinition)) then
    attrs := attrs.push m!"expose"

  if defeqAttr.hasTag (← getEnv) id then
    attrs := attrs.push m!"defeq"

  let mut m : MessageData := m!""
  unless attrs.isEmpty do
    m := m ++ "@[" ++ MessageData.joinSep attrs.toList ", " ++ "] "

  match safety with
  | DefinitionSafety.unsafe  => m := m ++ "unsafe "
  | DefinitionSafety.partial => m := m ++ "partial "
  | DefinitionSafety.safe    => pure ()

  let id' ← match privateToUserName? id with
    | some id' =>
      m := m ++ "private "
      pure id'
    | none =>
      pure id

  if isProtected (← getEnv) id then
    m := m ++ "protected "

  if isMarkedMeta (← getEnv) id then
    m := m ++ "meta "

  if sig then
    return m!"{m}{kind} {id'}{levelParamsToMessageData levelParams} : {type}"
  else
    return m!"{m}{kind}"

private def mkOmittedMsg : Option Expr → MessageData
  | none   => "<not imported>"
  | some e => e

private def printAxiomLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (safety : DefinitionSafety) : CommandElabM Unit := do
  logInfo (← mkHeader kind id levelParams type safety)

private def printDefLike (sigOnly : Bool) (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (value? : Option Expr) (safety := DefinitionSafety.safe) : CommandElabM Unit := do
  if sigOnly then
    printAxiomLike kind id levelParams type safety
  else
    let m ← mkHeader kind id levelParams type safety
    let m := m ++ " :=" ++ Format.line ++ mkOmittedMsg value?
    logInfo m

private def printQuot (id : Name) (levelParams : List Name) (type : Expr) : CommandElabM Unit := do
  printAxiomLike "Quotient primitive" id levelParams type (safety := DefinitionSafety.safe)

private def printInduct (id : Name) (levelParams : List Name) (numParams : Nat) (type : Expr)
    (ctors : List Name) (isUnsafe : Bool) : CommandElabM Unit := do
  let mut m ← mkHeader "inductive" id levelParams type (if isUnsafe then .unsafe else .safe)
  m := m ++ Format.line ++ "number of parameters: " ++ toString numParams
  m := m ++ Format.line ++ "constructors:"
  for ctor in ctors do
    let cinfo ← getConstInfo ctor
    m := m ++ Format.line ++ ctor ++ " : " ++ cinfo.type
  logInfo m

private def printRecursor (recInfo : RecursorVal) : CommandElabM Unit := do
  let mut m ← mkHeader "recursor" recInfo.name recInfo.levelParams recInfo.type (if recInfo.isUnsafe then .unsafe else .safe)
  m := m ++ Format.line ++ m!"number of parameters: {recInfo.numParams}"
  m := m ++ Format.line ++ m!"number of indices: {recInfo.numIndices}"
  m := m ++ Format.line ++ m!"number of motives: {recInfo.numMotives}"
  m := m ++ Format.line ++ m!"number of minors: {recInfo.numMinors}"
  if recInfo.k then
    m := m ++ Format.line ++ m!"supports k-like reduction"
  m := m ++ Format.line ++ "rules:"
  for rule in recInfo.rules do
    m := m ++ Format.line ++ m!"for {rule.ctor} ({rule.nfields} fields): {rule.rhs}"
  logInfo m

/--
Computes the origin of a field. Returns its `StructureFieldInfo` at the origin.
Multiple parents could be the origin of a field, but we say the first parent that provides it is the one that determines the origin.
-/
private partial def getFieldOrigin (structName field : Name) : MetaM StructureFieldInfo := do
  let env ← getEnv
  for parent in getStructureParentInfo env structName do
    if (findField? env parent.structName field).isSome then
      return ← getFieldOrigin parent.structName field
  let some fi := getFieldInfo? env structName field
    | throwError "no such field {field} in {structName}"
  return fi

open Meta in
private partial def printStructure (id : Name) (levelParams : List Name) (numParams : Nat) (type : Expr) (ctor : Name)
    (isUnsafe : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let kind := if isClass env id then "class" else "structure"
  let header ← mkHeader kind id levelParams type (if isUnsafe then .unsafe else .safe) (sig := false)
  let levels := levelParams.map Level.param
  liftTermElabM <| forallTelescope (← getConstInfo id).type fun params _ =>
    let s := Expr.const id levels
    withLocalDeclD `self (mkAppN s params) fun self => do
      let mut m : MessageData := header
      -- Signature
      m := m ++ " " ++ .ofFormatWithInfosM do
        let (stx, infos) ← PrettyPrinter.delabCore s (delab := PrettyPrinter.Delaborator.delabConstWithSignature)
        pure ⟨← PrettyPrinter.ppTerm ⟨stx⟩, infos⟩
      m := m ++ Format.line ++ m!"number of parameters: {numParams}"
      -- Parents
      let parents := getStructureParentInfo env id
      unless parents.isEmpty do
        m := m ++ Format.line ++ "parents:"
        for parent in parents do
          let ptype ← inferType (mkApp (mkAppN (.const parent.projFn levels) params) self)
          m := m ++ indentD m!"{.ofConstName parent.projFn (fullNames := true)} : {ptype}"
      -- Fields
      -- Collect autoParam tactics, which are all on the flat constructor:
      let flatCtorName := mkFlatCtorOfStructCtorName ctor
      let flatCtorInfo ← getConstInfo flatCtorName
      let autoParams : NameMap Syntax ← forallTelescope flatCtorInfo.type fun args _ =>
        args[numParams...*].foldlM (init := {}) fun set arg => do
          let decl ← arg.fvarId!.getDecl
          if let some (.const tacticDecl _) := decl.type.getAutoParamTactic? then
            let tacticSyntax ← ofExcept <| evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl
            pure <| set.insert decl.userName tacticSyntax
          else
            pure set
      let fields := getStructureFieldsFlattened env id (includeSubobjectFields := false)
      if fields.isEmpty then
        m := m ++ Format.line ++ "fields: (none)"
      else
        m := m ++ Format.line ++ "fields:"
        -- Map of fields to projections of `self`
        let fieldMap : NameMap Expr ← fields.foldlM (init := {}) fun fieldMap field => do
          pure <| fieldMap.insert field (← mkProjection self field)
        for field in fields do
          let some source := findField? env id field | panic! "missing structure field info"
          let fi ← getFieldOrigin source field
          let proj := fi.projFn
          let modifier := if isPrivateName proj then "private " else ""
          let ftype ← inferType (fieldMap.get! field)
          let value ←
            if let some stx := autoParams.find? field then
              let stx : TSyntax ``Parser.Tactic.tacticSeq := ⟨stx⟩
              pure m!" := by{indentD stx}"
            else if let some defFn := getEffectiveDefaultFnForField? env id field then
              if let some (_, val) ← instantiateStructDefaultValueFn? defFn levels params (pure ∘ fieldMap.find?) then
                pure m!" :={indentExpr val}"
              else
                pure m!" := <error>"
            else
              pure m!""
          m := m ++ indentD (m!"{modifier}{.ofConstName proj (fullNames := true)} : {MessageData.nest 2 ftype}{value}")
      -- Constructor
      let cinfo := getStructureCtor (← getEnv) id
      let ctorModifier := if isPrivateName cinfo.name then "private " else ""
      m := m ++ Format.line ++ "constructor:" ++ indentD (ctorModifier ++ .signature cinfo.name)
      -- Resolution order
      let resOrder ← getStructureResolutionOrder id
      if resOrder.size > 1 then
        m := m ++ Format.line ++ "field notation resolution order:"
          ++ indentD (MessageData.joinSep (resOrder.map (.ofConstName · (fullNames := true))).toList ", ")
      -- Omit proofs; the delaborator enables `pp.proofs` for non-constant proofs, but we don't want this for default values
      withOptions (fun opts => opts.set pp.proofs.name false) do
        logInfo m

private def printIdCore (sigOnly : Bool) (id : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? id with
  | ConstantInfo.axiomInfo { levelParams := us, type := t, isUnsafe := u, .. } =>
    match getOriginalConstKind? env id with
    | some .defn => printDefLike sigOnly "def" id us t none (if u then .unsafe else .safe)
    | some .thm => printDefLike sigOnly "theorem" id us t none (if u then .unsafe else .safe)
    | _  => printAxiomLike "axiom" id us t (if u then .unsafe else .safe)
  | ConstantInfo.defnInfo  { levelParams := us, type := t, value := v, safety := s, .. } => printDefLike sigOnly "def" id us t v s
  | ConstantInfo.thmInfo  { levelParams := us, type := t, value := v, .. } => printDefLike sigOnly "theorem" id us t v
  | ConstantInfo.opaqueInfo  { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "opaque" id us t (if u then .unsafe else .safe)
  | ConstantInfo.quotInfo  { levelParams := us, type := t, .. } => printQuot id us t
  | ConstantInfo.ctorInfo { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "constructor" id us t (if u then .unsafe else .safe)
  | ConstantInfo.recInfo recInfo => printRecursor recInfo
  | ConstantInfo.inductInfo { levelParams := us, numParams, type := t, ctors, isUnsafe := u, .. } =>
    if isStructure env id then
      printStructure id us numParams t ctors[0]! u
    else
      printInduct id us numParams t ctors u
  | none => throwUnknownId id

private def printId (id : Syntax) : CommandElabM Unit := do
  addCompletionInfo <| CompletionInfo.id id id.getId (danglingDot := false) {} none
  let cs ← liftCoreM <| realizeGlobalConstWithInfos id
  cs.forM (printIdCore (sigOnly := false) ·)

@[builtin_command_elab «print»] def elabPrint : CommandElab
  | `(#print%$tk $id:ident) => withRef tk <| printId id
  | `(#print%$tk $s:str)    => logInfoAt tk s.getString
  | _                       => throwError "invalid #print command"

private def printIdSig (id : Syntax) : CommandElabM Unit := do
  addCompletionInfo <| CompletionInfo.id id id.getId (danglingDot := false) {} none
  let cs ← liftCoreM <| realizeGlobalConstWithInfos id
  cs.forM (printIdCore (sigOnly := true) ·)

@[builtin_command_elab «printSig»] def elabPrintSig : CommandElab := fun stx =>
  withRef stx[0] do
    let id := stx[2]
    printIdSig id

private def printAxiomsOf (constName : Name) : CommandElabM Unit := do
  let axioms ← collectAxioms constName
  if axioms.isEmpty then
    logInfo m!"'{constName}' does not depend on any axioms"
  else
    logInfo m!"'{constName}' depends on axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"

@[builtin_command_elab «printAxioms»] def elabPrintAxioms : CommandElab
  | `(#print%$tk axioms $id) => withRef tk do
    if (← getEnv).header.isModule then
      throwError "cannot use `#print axioms` in a `module`; consider temporarily removing the \
        `module` header or placing the command in a separate file"

    let cs ← liftCoreM <| realizeGlobalConstWithInfos id
    cs.forM printAxiomsOf
  | _ => throwUnsupportedSyntax

private def printEqnsOf (constName : Name) : CommandElabM Unit := do
  let some eqns ← liftTermElabM <| Meta.getEqnsFor? constName |
    logInfo m!"'{constName}' does not have equations"
  let mut m := m!"equations:"
  for eq in eqns do
    let cinfo ← getConstInfo eq
    m := m ++ Format.line ++ (← mkHeader "theorem" eq cinfo.levelParams cinfo.type .safe)
  logInfo m

@[builtin_command_elab «printEqns»] def elabPrintEqns : CommandElab := fun stx => do
  let id := stx[2]
  let cs ← liftCoreM <| realizeGlobalConstWithInfos id
  cs.forM printEqnsOf

end Lean.Elab.Command
