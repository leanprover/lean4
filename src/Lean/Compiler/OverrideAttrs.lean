/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module
prelude
import Lean.Compiler.InductiveOverride
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.InlineAttrs
import Lean.Compiler.NoncomputableAttr
import Lean.Meta.Tactic.Simp
import Lean.Elab.Tactic

namespace Lean.Compiler

open LCNF ImpureType

builtin_initialize
  registerBuiltinAttribute {
    name := `override_runtime_type
    descr := "override impure type of a declaration"
    add := fun declName stx kind => do
      unless kind == .global do
        throwAttrMustBeGlobal `override_runtime_type kind
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule `override_runtime_type declName
      if hasInductiveOverride env declName then
        throwError "`{declName}` already has an override, cannot apply another"
      if ← didCompileInductive declName then
        throwError "The `[override_runtime_type]` attribute cannot be used after the declaration"
      let type := (← getConstVal declName).type
      unless ← (Meta.isTypeFormerType type).run' do
        throwError "Invalid `[override_runtime_type]` attribute, the declaration isn't a type"
      let typeIdent? ← Attribute.Builtin.getIdent? stx
      let impureType : Expr := .const ((typeIdent?.map (·.getId)).getD `tobj) []
      unless impureType.isValidImpureType do
        throwErrorAt typeIdent?.get! "`{typeIdent?}` is not a valid impure type"
      let incomplete := typeIdent?.isNone
      modifyEnv (addInductiveOverride · (.simpleType declName impureType incomplete))
    applicationTime := .afterTypeChecking
  }

def checkNotComputable (thing : String) (declName : Name) : CoreM Unit := do
  unless isNoncomputable (← getEnv) declName do
    throwError "Invalid `[compiled_cases]` attribute, the {thing} `{.ofConstName declName}` \
      must be noncomputable"
  if (getImplementedBy? (← getEnv) declName).isSome then
    throwError "Invalid `[compiled_cases]` attribute, the {thing} `{.ofConstName declName}` \
      must not have an `[implemented_by]` attribute"
  if isExtern (← getEnv) declName then
    throwError "Invalid `[compiled_cases]` attribute, the {thing} `{.ofConstName declName}` \
      must not have an `[extern]` attribute"
  if (CSimp.ext.getState (← getEnv)).map.contains declName then
    throwError "Invalid `[compiled_cases]` attribute, the {thing} `{.ofConstName declName}` \
      must not have a `[csimp]` lemma"
  if hasMacroInlineAttribute (← getEnv) declName then
    throwError "Invalid `[compiled_cases]` attribute, the {thing} `{.ofConstName declName}` \
      must not have a `[macro_inline]` attribute"
  if hasInductiveOverride (← getEnv) declName then
    throwError "Invalid `[compiled_cases]` attribute, the {thing} `{.ofConstName declName}` \
      already has an override"

/-- Note: `targetDecl` is assumed to be in the same module -/
partial def declDependsOnDecl (declName : Name) (targetDecl : Name) : StateT (NameMap Bool) CoreM Bool := do
  if let some res := (← get).find? declName then
    return res
  unless ((← getEnv).getModuleIdx? declName).isNone do
    return false
  modify fun s => s.insert declName false
  let info ← getConstInfo declName
  for nm in info.getUsedConstantsAsSet do
    if ← declDependsOnDecl nm targetDecl then
      modify fun s => s.insert declName true
      return true
  return false

def exprDependsOnDecl (e : Expr) (targetDecl : Name) : StateT (NameMap Bool) CoreM Bool := do
  e.getUsedConstants.anyM (declDependsOnDecl · targetDecl)

open Meta

def proveEquation (p : Expr) (declName : Name) : MetaM Unit := do
  let goal ← mkFreshExprMVar p
  let tactic ← `(tactic| first | simp; done | rfl)
  try
    (Elab.Tactic.evalTactic tactic).run { elaborator := .anonymous } |>.run'
      { goals := [goal.mvarId!] } |>.run'
  catch _ex =>
    let hint := m!"You can first prove the missing equations as simp lemmas and then use \
      `attribute [compiled_cases] {declName}`"
    throwError "Failed to prove equation using `simp` or `rfl`\n\n{goal.mvarId!}{.hint' hint}"
  let result ← instantiateMVars goal
  if result.hasMVar then
    throwError "Proof of equation has metavariables\n\n{goal.mvarId!}"

def validateCases (declName : Name) : MetaM Unit := do
  let val ← getConstInfo declName
  let isUnsafe := val.isUnsafe || val.isPartial
  forallTelescope val.type fun vars ret => do
    let motive := ret.getAppFn
    unless motive.isFVar do
      throwError "Invalid `[compiled_cases]` attribute, expected the result type to be an \
        application of the motive but found:{indentExpr ret}"
    let elimLvl ← getLevel ret
    let .param elimLParam := elimLvl |
      throwError "Invalid `[compiled_cases]` attribute, the eliminator must be able to eliminate \
        into any universe"
    let nparams := vars.idxOf motive
    let motiveArgs := ret.getAppArgs
    if motiveArgs.isEmpty then
      throwError "Invalid `[compiled_cases]` attribute, cannot have a nullary motive"
    let nindices := motiveArgs.size - 1
    let indicesAndMajor := vars[(nparams + 1)...(nparams + 1 + nindices + 1)].toArray
    unless motiveArgs == indicesAndMajor do
      throwError "Invalid `[compiled_cases]` attribute, the arguments to the motive must be \
        the indices and the major premise, which should come directly after the motive in
        the argument list"
    let expectedMotiveType ← mkForallFVars indicesAndMajor (.sort elimLvl)
    let motiveType ← inferType motive
    unless motiveType == expectedMotiveType do
      throwError "Invalid `[compiled_cases]` attribute, expected motive to have type\
        {indentExpr expectedMotiveType}\n\
        but found{indentExpr motiveType}"
    let params := vars[0...nparams].toArray
    let indices := vars[(nparams + 1)...(nparams + 1 + nindices)].toArray
    let majorType ← inferType vars[nparams + 1 + nindices]!
    let .const indName lparams := majorType.getAppFn |
      throwError "Invalid `[compiled_cases]` attribute, expected major premise's type to be a \
        constant application but found:{majorType}"
    unless lparams.all (·.isParam) do
      throwError "Invalid `[compiled_cases]` attribute, the eliminator must be completely \
        universe polymorphic"
    let levelParams := lparams.map fun | .param nm => nm | _ => unreachable!
    unless (elimLParam :: levelParams).Nodup do
      throwError "Invalid `[compiled_cases]` attribute, the eliminator must be completely \
        universe polymorphic"
    unless majorType == mkAppN (mkAppN (.const indName lparams) params) indices do
      throwError "Invalid `[compiled_cases]` attribute, the major premise's type arguments \
        must be the parameters and indices of the eliminator but found:\
        {indentExpr (majorType.setPPExplicit true)}"
    let minors := vars[(nparams + 1 + nindices + 1)...*]
    let mut ctors : Array (Name × Nat) := #[] -- name + numFields
    let mut isRec := (incompleteRefExt.getState (← getEnv)).contains indName
    let mut dependencyState : NameMap Bool := {}
    for minor in minors do
      let minorType ← inferType minor
      forallTelescope minorType fun fields body => do←
        unless body.getAppFn == motive do
          throwError "Invalid `[compiled_cases]` attribute, expected result type of \
            minor premise `{minor}` to be an application of the motive but found:{indentExpr body}"
        let arg := body.appArg!
        let .const ctorName lparams' := arg.getAppFn |
          throwError "Invalid `[compiled_cases]` attribute, expected argument of the motive in the \
            minor premise `{minor}` to be a constant application:{indentExpr body}"
        if lparams != lparams' then
          throwError "Invalid `[compiled_cases]` attribute, the constructor \
            `{arg.getAppFn.setPPUniverses true}` has different level params from the type \
            `{majorType.getAppFn.setPPUniverses true}`{.hint'
            "You may need to make the level parameters explicit in the definition of the constructor"}"
        unless arg.getAppArgs == params ++ fields do
          throwError "Invalid `[compiled_cases]` attribute, the arguments to the constructor \
            must be the parameters of the eliminator and the fields of the minor premise but found:\
            {indentExpr (arg.setPPExplicit true)}"
        for field in fields do
          let fieldType ← inferType field
          unless isRec do
            (isRec, dependencyState) ← (withoutExporting <| exprDependsOnDecl fieldType indName).run dependencyState
          let isValidFVar (f : Expr) : Bool :=
            params.contains f || fields.contains f
          if fieldType.hasAnyFVar (fun f => !isValidFVar (.fvar f)) then
            throwError "Invalid `[compiled_cases]` attribute, the fields in the minor premise \
              `{minor}` may only depend on parameters and other fields but found:\
              {indentD (field ++ " : " ++ fieldType)}"
        ctors := ctors.push (ctorName, fields.size)
    ---- end of syntactic checks ----
    unless ((← getEnv).getModuleIdxFor? indName).isNone do
      throwError "Invalid `[compiled_cases]` attribute, the type `{.ofConstName indName}` must be \
        defined in the same module"
    checkNotComputable "eliminator" declName
    for (ctor, _) in ctors do
      checkNotComputable "constructor" ctor
    let some (.simpleType _ _ (incomplete := true)) := getInductiveOverride? (← getEnv) indName |
      throwError "Invalid `[compiled_cases]` attribute, the type `{.ofConstName indName}` must be \
        tagged with the attribute `[override_runtime_type]` without arguments"
    if isUnsafe then
      for (ctor, _) in ctors do
        unless (← getConstInfo ctor).isUnsafe do
          throwError "Invalid `[compiled_cases]` attribute, the eliminator is unsafe but the \
            constructor `{ctor}` is not"
    else
      for minor in minors do
        let minorType ← inferType minor
        forallTelescope minorType fun fields body => do
          let motiveArgs := body.getAppArgs
          let recApp := mkAppN (.const declName (val.levelParams.map .param)) params
          let recApp := recApp.app motive
          let recApp := mkAppN recApp motiveArgs
          let recApp := mkAppN recApp minors
          let minorApp := mkAppN minor fields
          let equation := mkApp3 (.const ``Eq [elimLvl]) body recApp minorApp
          proveEquation equation declName
    let mut cidx := 0
    for (ctor, nfields) in ctors do
      let override := .constructor ctor {
        induct := indName
        cidx := cidx
        numParams := nparams
        numFields := nfields
      }
      modifyEnv (addInductiveOverride · override)
    let override := .inductiveType indName {
      numParams := nparams
      ctors := ctors.map (·.1) |>.toList
      isRec
    }
    modifyEnv (addInductiveOverride · override)
    compileDecls #[indName]
    let override := .isCases declName
    modifyEnv (addInductiveOverride · override)

builtin_initialize
  registerBuiltinAttribute {
    name := `compiled_cases
    descr := "declare a casesOn-like eliminator as the canonical (to the compiler) casesOn"
    add := fun declName stx kind => do
      unless kind == .global do
        throwAttrMustBeGlobal `compiled_cases kind
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule `compiled_cases declName
      MetaM.run' <| validateCases declName
    applicationTime := .afterTypeChecking
  }

end Lean.Compiler
