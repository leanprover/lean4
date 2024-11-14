/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Eqns
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace Lean.Elab.Command

private def throwUnknownId (id : Name) : CommandElabM Unit :=
  throwError "unknown identifier '{.ofConstName id}'"

private def levelParamsToMessageData (levelParams : List Name) : MessageData :=
  match levelParams with
  | []    => ""
  | u::us => Id.run do
    let mut m := m!".\{{u}"
    for u in us do
      m := m ++ ", " ++ toMessageData u
    return m ++ "}"

private def mkHeader (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (safety : DefinitionSafety) : CommandElabM MessageData := do
  let m : MessageData :=
    match (← getReducibilityStatus id) with
    | ReducibilityStatus.irreducible => "@[irreducible] "
    | ReducibilityStatus.reducible => "@[reducible] "
    | ReducibilityStatus.semireducible => ""
  let m :=
    m ++
    match safety with
    | DefinitionSafety.unsafe  => "unsafe "
    | DefinitionSafety.partial => "partial "
    | DefinitionSafety.safe    => ""
  let m := if isProtected (← getEnv) id then m ++ "protected " else m
  let (m, id) := match privateToUserName? id with
    | some id => (m ++ "private ", id)
    | none    => (m, id)
  let m := m ++ kind ++ " " ++ id ++ levelParamsToMessageData levelParams ++ " : " ++ type
  pure m

private def mkHeader' (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (isUnsafe : Bool) : CommandElabM MessageData :=
  mkHeader kind id levelParams type (if isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe)

private def printDefLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (value : Expr) (safety := DefinitionSafety.safe) : CommandElabM Unit := do
  let m ← mkHeader kind id levelParams type safety
  let m := m ++ " :=" ++ Format.line ++ value
  logInfo m

private def printAxiomLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (isUnsafe := false) : CommandElabM Unit := do
  logInfo (← mkHeader' kind id levelParams type isUnsafe)

private def printQuot (id : Name) (levelParams : List Name) (type : Expr) : CommandElabM Unit := do
  printAxiomLike "Quotient primitive" id levelParams type

private def printInduct (id : Name) (levelParams : List Name) (numParams : Nat) (type : Expr)
    (ctors : List Name) (isUnsafe : Bool) : CommandElabM Unit := do
  let mut m ← mkHeader' "inductive" id levelParams type isUnsafe
  m := m ++ Format.line ++ "number of parameters: " ++ toString numParams
  m := m ++ Format.line ++ "constructors:"
  for ctor in ctors do
    let cinfo ← getConstInfo ctor
    m := m ++ Format.line ++ ctor ++ " : " ++ cinfo.type
  logInfo m

open Meta in
private def printStructure (id : Name) (levelParams : List Name) (numParams : Nat) (type : Expr)
    (ctor : Name) (fields : Array Name) (isUnsafe : Bool) (isClass : Bool) : CommandElabM Unit := do
  let kind := if isClass then "class" else "structure"
  let mut m ← mkHeader' kind id levelParams type isUnsafe
  m := m ++ Format.line ++ "number of parameters: " ++ toString numParams
  m := m ++ Format.line ++ "constructor:"
  let cinfo ← getConstInfo ctor
  m := m ++ Format.line ++ ctor ++ " : " ++ cinfo.type
  m := m ++ Format.line ++ "fields:" ++ (← doFields)
  logInfo m
where
  doFields := liftTermElabM do
    forallTelescope (← getConstInfo id).type fun params _ =>
      withLocalDeclD `self (mkAppN (Expr.const id (levelParams.map .param)) params) fun self => do
        let params := params.push self
        let mut m : MessageData := ""
        for field in fields do
          match getProjFnForField? (← getEnv) id field with
          | some proj =>
            let field : Format := if isPrivateName proj then "private " ++ toString field else toString field
            let cinfo ← getConstInfo proj
            let ftype ← instantiateForall cinfo.type params
            m := m ++ Format.line ++ field ++ " : " ++ ftype
          | none => panic! "missing structure field info"
        addMessageContext m

private def printIdCore (id : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? id with
  | ConstantInfo.axiomInfo { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "axiom" id us t u
  | ConstantInfo.defnInfo  { levelParams := us, type := t, value := v, safety := s, .. } => printDefLike "def" id us t v s
  | ConstantInfo.thmInfo  { levelParams := us, type := t, value := v, .. } => printDefLike "theorem" id us t v
  | ConstantInfo.opaqueInfo  { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "opaque" id us t u
  | ConstantInfo.quotInfo  { levelParams := us, type := t, .. } => printQuot id us t
  | ConstantInfo.ctorInfo { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "constructor" id us t u
  | ConstantInfo.recInfo { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "recursor" id us t u
  | ConstantInfo.inductInfo { levelParams := us, numParams, type := t, ctors, isUnsafe := u, .. } =>
    match getStructureInfo? env id with
    | some { fieldNames, .. } =>
      let [ctor] := ctors | panic! "structures have only one constructor"
      printStructure id us numParams t ctor fieldNames u (isClass env id)
    | none => printInduct id us numParams t ctors u
  | none => throwUnknownId id

private def printId (id : Syntax) : CommandElabM Unit := do
  addCompletionInfo <| CompletionInfo.id id id.getId (danglingDot := false) {} none
  let cs ← liftCoreM <| realizeGlobalConstWithInfos id
  cs.forM printIdCore

@[builtin_command_elab «print»] def elabPrint : CommandElab
  | `(#print%$tk $id:ident) => withRef tk <| printId id
  | `(#print%$tk $s:str)    => logInfoAt tk s.getString
  | _                       => throwError "invalid #print command"

private def printAxiomsOf (constName : Name) : CommandElabM Unit := do
  let axioms ← collectAxioms constName
  if axioms.isEmpty then
    logInfo m!"'{constName}' does not depend on any axioms"
  else
    logInfo m!"'{constName}' depends on axioms: {axioms.qsort Name.lt |>.toList}"

@[builtin_command_elab «printAxioms»] def elabPrintAxioms : CommandElab
  | `(#print%$tk axioms $id) => withRef tk do
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
