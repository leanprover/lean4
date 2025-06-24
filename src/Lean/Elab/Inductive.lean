/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kyle Miller
-/
prelude
import Lean.Elab.MutualInductive

namespace Lean.Elab.Command
open Meta

/-
```
def Lean.Parser.Command.«inductive» :=
  leading_parser "inductive " >> declId >> optDeclSig >> optional ("where" <|> ":=") >> many ctor

def Lean.Parser.Command.classInductive :=
  leading_parser atomic (group ("class " >> "inductive ")) >> declId >> optDeclSig >> optional ("where" <|> ":=") >> many ctor >> optDeriving
```
-/
private def inductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) : TermElabM InductiveView := do
  let isClass := decl.isOfKind ``Parser.Command.classInductive
  let modifiers := if isClass then modifiers.addAttr { name := `class } else modifiers
  let (binders, type?) := expandOptDeclSig decl[2]
  let declId           := decl[1]
  let ⟨name, declName, levelNames⟩ ← Term.expandDeclId (← getCurrNamespace) (← Term.getLevelNames) declId modifiers
  addDeclarationRangesForBuiltin declName modifiers.stx decl
  let ctors      ← decl[4].getArgs.mapM fun ctor => withRef ctor do
    /-
    ```
    def ctor := leading_parser optional docComment >> "\n| " >> declModifiers >> rawIdent >> optDeclSig
    ```
    -/
    let mut ctorModifiers ← elabModifiers ⟨ctor[2]⟩
    if let some leadingDocComment := ctor[0].getOptional? then
      if ctorModifiers.docString?.isSome then
        logErrorAt leadingDocComment "duplicate doc string"
      ctorModifiers := { ctorModifiers with docString? := some ⟨leadingDocComment⟩ }
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      throwError "invalid 'private' constructor in a 'private' inductive datatype"
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "invalid 'protected' constructor in a 'private' inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 3
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[3] <| applyVisibility ctorModifiers.visibility ctorName
    let (binders, type?) := expandOptDeclSig ctor[4]
    addDocString' ctorName ctorModifiers.docString?
    addDeclarationRangesFromSyntax ctorName ctor ctor[3]
    return { ref := ctor, declId := ctor[3], modifiers := ctorModifiers, declName := ctorName, binders := binders, type? := type? : CtorView }
  let computedFields ← (decl[5].getOptional?.map (·[1].getArgs) |>.getD #[]).mapM fun cf => withRef cf do
    return { ref := cf, modifiers := cf[0], fieldId := cf[1].getId, type := ⟨cf[3]⟩, matchAlts := ⟨cf[4]⟩ }
  let classes ← getOptDerivingClasses decl[6]
  if decl[3][0].isToken ":=" then
    -- https://github.com/leanprover/lean4/issues/5236
    withRef decl[0] <| Linter.logLintIf Linter.linter.deprecated decl[3]
      "'inductive ... :=' has been deprecated in favor of 'inductive ... where'."
  return {
    ref             := decl
    shortDeclName   := name
    derivingClasses := classes
    allowIndices    := true
    allowSortPolymorphism := true
    declId, modifiers, isClass, declName, levelNames
    binders, type?, ctors
    computedFields
  }

private def isInductiveFamily (numParams : Nat) (indFVar : Expr) : TermElabM Bool := do
  let indFVarType ← inferType indFVar
  forallTelescopeReducing indFVarType fun xs _ =>
    return xs.size > numParams

private def getArrowBinderNames (type : Expr) : Array Name :=
  go type #[]
where
  go (type : Expr) (acc : Array Name) : Array Name :=
    match type with
    | .forallE n _ b _ => go b (acc.push n)
    | .mdata _ b       => go b acc
    | _ => acc

/--
Replaces binder names in `type` with `newNames`.
Remark: we only replace the names for binder containing macroscopes.
-/
private def replaceArrowBinderNames (type : Expr) (newNames : Array Name) : Expr :=
  go type 0
where
  go (type : Expr) (i : Nat) : Expr :=
    if h : i < newNames.size then
      match type with
      | .forallE n d b bi =>
        if n.hasMacroScopes then
          mkForall newNames[i] bi d (go b (i+1))
        else
          mkForall n bi d (go b (i+1))
      | _ => type
    else
      type

/--
Reorders constructor arguments to improve the effectiveness of the `fixedIndicesToParams` method.

The idea is quite simple. Given a constructor type of the form
```
(a₁ : A₁) → ... → (aₙ : Aₙ) → C b₁ ... bₘ
```
We try to find the longest prefix `b₁ ... bᵢ`, `i ≤ m` s.t.
- each `bₖ` is in `{a₁, ..., aₙ}`
- each `bₖ` only depends on variables in `{b₁, ..., bₖ₋₁}`

Then, it moves this prefix `b₁ ... bᵢ` to the front.

Remark: We only reorder implicit arguments that have macroscopes. See issue #1156.
The macroscope test is an approximation, we could have restricted ourselves to auto-implicit arguments.
-/
private def reorderCtorArgs (ctorType : Expr) : MetaM Expr := do
  forallTelescopeReducing ctorType fun as type => do
    /- `type` is of the form `C ...` where `C` is the inductive datatype being defined. -/
    let bs := type.getAppArgs
    let mut as  := as
    let mut bsPrefix := #[]
    for b in bs do
      unless b.isFVar && as.contains b do
        break
      let localDecl ← getFVarLocalDecl b
      if localDecl.binderInfo.isExplicit then
        break
      unless localDecl.userName.hasMacroScopes do
        break
      if (← localDeclDependsOnPred localDecl fun fvarId => as.any fun p => p.fvarId! == fvarId) then
        break
      bsPrefix := bsPrefix.push b
      as := as.erase b
    if bsPrefix.isEmpty then
      return ctorType
    else
      let r ← mkForallFVars (bsPrefix ++ as) type
      /- `r` already contains the resulting type.
         To be able to produce better error messages, we copy the first `bsPrefix.size` binder names from `C` to `r`.
         This is important when some of constructor parameters were inferred using the auto-bound implicit feature.
         For example, in the following declaration.
         ```
          inductive Member : α → List α → Type u
            | head : Member a (a::as)
            | tail : Member a bs → Member a (b::bs)
         ```
         if we do not copy the binder names
         ```
         #check @Member.head
         ```
         produces `@Member.head : {x : Type u_1} → {a : x} → {as : List x} → Member a (a :: as)`
         which is correct, but a bit confusing. By copying the binder names, we obtain
         `@Member.head : {α : Type u_1} → {a : α} → {as : List α} → Member a (a :: as)`
       -/
      let C := type.getAppFn
      let binderNames := getArrowBinderNames (← instantiateMVars (← inferType C))
      return replaceArrowBinderNames r binderNames[:bsPrefix.size]

/--
  Elaborate constructor types.

  Remark: we check whether the resulting type is correct, and the parameter occurrences are consistent, but
  we currently do not check for:
  - Positivity (it is a rare failure, and the kernel already checks for it).
  - Universe constraints (the kernel checks for it).
-/
private def elabCtors (indFVars : Array Expr) (params : Array Expr) (r : ElabHeaderResult) : TermElabM (List Constructor) :=
  withRef r.view.ref do
  withExplicitToImplicit params do
  let indFVar := r.indFVar
  let indFamily ← isInductiveFamily params.size indFVar
  r.view.ctors.toList.mapM fun ctorView =>
    Term.withAutoBoundImplicit <| Term.elabBinders ctorView.binders.getArgs fun ctorParams =>
      withRef ctorView.ref do
        let elabCtorType : TermElabM Expr := do
          match ctorView.type? with
          | none          =>
            if indFamily then
              throwError "Missing resulting type for constructor '{ctorView.declName}': \
                Its resulting type must be specified because it is part of an inductive family declaration"
            return mkAppN indFVar params
          | some ctorType =>
            let type ← Term.elabType ctorType
            trace[Elab.inductive] "elabType {ctorView.declName} : {type} "
            Term.synthesizeSyntheticMVars (postpone := .yes)
            let type ← instantiateMVars type
            let type ← checkParamOccs type
            forallTelescopeReducing type fun _ resultingType => do
              unless resultingType.getAppFn == indFVar do
                throwUnexpectedResultingTypeMismatch resultingType indFVar ctorView.declName ctorType
              unless (← isType resultingType) do
                throwUnexpectedResultingTypeNotType resultingType ctorView.declName ctorType
            return type
        let type ← elabCtorType
        Term.synthesizeSyntheticMVarsNoPostponing
        let ctorParams ← Term.addAutoBoundImplicits ctorParams (ctorView.declId.getTailPos? (canonicalOnly := true))
        let except (mvarId : MVarId) := ctorParams.any fun ctorParam => ctorParam.isMVar && ctorParam.mvarId! == mvarId
        /-
          We convert metavariables in the resulting type into extra parameters. Otherwise, we would not be able to elaborate
          declarations such as
          ```
          inductive Palindrome : List α → Prop where
            | nil      : Palindrome [] -- We would get an error here saying "failed to synthesize implicit argument" at `@List.nil ?m`
            | single   : (a : α) → Palindrome [a]
            | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])
          ```
          We used to also collect unassigned metavariables on `ctorParams`, but it produced counterintuitive behavior.
          For example, the following declaration used to be accepted.
          ```
          inductive Foo
          | bar (x)

          #check Foo.bar
          -- @Foo.bar : {x : Sort u_1} → x → Foo
          ```
          which is also inconsistent with the behavior of auto implicits in definitions. For example, the following example was never accepted.
          ```
          def bar (x) := 1
          ```
        -/
        let extraCtorParams ← Term.collectUnassignedMVars (← instantiateMVars type) #[] except
        trace[Elab.inductive] "extraCtorParams: {extraCtorParams}"
        /- We must abstract `extraCtorParams` and `ctorParams` simultaneously to make
            sure we do not create auxiliary metavariables. -/
        let type ← mkForallFVars (extraCtorParams ++ ctorParams) type
        let type ← reorderCtorArgs type
        let type ← mkForallFVars params type
        trace[Elab.inductive] "{ctorView.declName} : {type}"
        return { name := ctorView.declName, type }
where
  /--
  Ensures that the arguments to recursive occurrences of the type family being defined match the
  parameters from the inductive definition.
  -/
  checkParamOccs (ctorType : Expr) : MetaM Expr :=
    let visit (e : Expr) : StateT (List Expr) MetaM TransformStep := do
      let f := e.getAppFn
      if indFVars.contains f then
        let mut args := e.getAppArgs
        -- Prefer throwing an "argument mismatch" error rather than a "missing parameter" one
        for i in [:min args.size params.size] do
          let param := params[i]!
          let arg := args[i]!
          unless (← isDefEq param arg) do
            let (arg, param) ← addPPExplicitToExposeDiff arg param
            let msg := m!"Mismatched inductive type parameter in{indentExpr e}\nThe provided argument\
              {indentExpr arg}\nis not definitionally equal to the expected parameter{indentExpr param}"
            let noteMsg := m!"The value of parameter '{param}' must be fixed throughout the inductive \
              declaration. Consider making this parameter an index if it must vary."
            throwNamedError lean.inductiveParamMismatch (msg ++ .note noteMsg)
          args := args.set! i param
        unless args.size ≥ params.size do
          let expected := mkAppN f params
          let containingExprMsg := (← get).head?.map toMessageData |>.getD m!"<missing>"
          let msg :=
            m!"Missing parameter(s) in occurrence of inductive type: In the expression{indentD containingExprMsg}\n\
               found{indentExpr e}\nbut expected all parameters to be specified:{indentExpr expected}"
          let noteMsg :=
            m!"All occurrences of an inductive type in the types of its constructors must specify its \
              fixed parameters. Only indices can be omitted in a partial application of the type constructor."
          throwNamedError lean.inductiveParamMissing (msg ++ .note noteMsg)
        return TransformStep.done (mkAppN f args)
      else
        modify fun es => e :: es
        return .continue
    let popContainingExpr (e : Expr) : StateT (List Expr) MetaM TransformStep := do
      modify fun es => es.drop 1
      return .done e
    transform ctorType (pre := visit) (post := popContainingExpr) |>.run' [ctorType]

  throwUnexpectedResultingTypeMismatch (resultingType indFVar : Expr) (declName : Name) (ctorType : Syntax) := do
    let lazyAppMsg := MessageData.ofLazyM do
      if let some fvarId := indFVar.fvarId? then
        if let some decl := (← getLCtx).find? fvarId then
          if (← whnfD decl.type).isForall then
            return m!" an application of"
      return m!""
    throwNamedErrorAt ctorType lean.ctorResultingTypeMismatch "Unexpected resulting type for constructor '{declName}': \
      Expected{lazyAppMsg}{indentExpr indFVar}\nbut found{indentExpr resultingType}"

  throwUnexpectedResultingTypeNotType (resultingType : Expr) (declName : Name) (ctorType : Syntax) := do
    let lazyMsg := MessageData.ofLazyM do
      let resultingTypeType ← inferType resultingType
      return indentExpr resultingTypeType
    throwNamedErrorAt ctorType lean.ctorResultingTypeMismatch "Unexpected resulting type for constructor '{declName}': \
      Expected a type, but found{indentExpr resultingType}\nof type{lazyMsg}"

@[builtin_inductive_elab Lean.Parser.Command.inductive, builtin_inductive_elab Lean.Parser.Command.classInductive]
def elabInductiveCommand : InductiveElabDescr where
  mkInductiveView (modifiers : Modifiers) (stx : Syntax) := do
    let view ← inductiveSyntaxToView modifiers stx
    return {
      view
      elabCtors := fun rs r params => do
        let ctors ← elabCtors (rs.map (·.indFVar)) params r
        return { ctors }
    }

end Lean.Elab.Command
