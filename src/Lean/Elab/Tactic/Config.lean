/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kyle Miller
-/
module

prelude
public import Lean.Meta.Eval
public import Lean.Elab.SyntheticMVars
public import Lean.Elab.Command
import Lean.Linter.MissingDocs

public section

namespace Lean.Elab.Tactic
open Meta Parser.Tactic Command

builtin_initialize
  registerTraceClass `Elab.tacticConfig

register_builtin_option debug.Elab.tacticConfig.forceEval : Bool := {
  defValue := false
  descr    := "force using the compiler to evaluate tactic configurations"
}

structure ConfigItemView where
  ref : Syntax
  option : Ident
  value : Term
  /-- Whether this was using `+`/`-`, to be able to give a better error message on type mismatch. -/
  bool : Bool := false

/-- Interprets the `config` as an array of option/value pairs. -/
def mkConfigItemViews (c : TSyntaxArray ``configItem) : Array ConfigItemView :=
  c.map fun item =>
    match item with
    | `(configItem| ($option:ident := $value)) => { ref := item, option, value }
    | `(configItem| +$option) => { ref := item, option, bool := true, value := mkCIdentFrom item ``true }
    | `(configItem| -$option) => { ref := item, option, bool := true, value := mkCIdentFrom item ``false }
    | `(config| (config%$tk := $value)) => { ref := item, option := mkCIdentFrom tk `config, value := value }
    | _ => { ref := item, option := ⟨Syntax.missing⟩, value := ⟨Syntax.missing⟩ }

/--
Expands a field access into full field access like `toB.toA.x`.
Returns that and the last projection function for `x` itself.
-/
private def expandFieldName (structName : Name) (fieldName : Name) : MetaM (Name × Name) := do
  let env ← getEnv
  unless isStructure env structName do throwError "`{.ofConstName structName}` is not a structure"
  let some baseStructName := findField? env structName fieldName
    | throwError "Structure `{.ofConstName structName}` does not have a field named `{fieldName}`"
  let some path := getPathToBaseStructure? env baseStructName structName
    | throwError "Internal error: Failed to access field `{fieldName}` in parent structure"
  let field := path.foldl (init := .anonymous) (fun acc s => Name.appendCore acc <| Name.mkSimple s.getString!) ++ fieldName
  let fieldInfo := (getFieldInfo? env baseStructName fieldName).get!
  return (field, fieldInfo.projFn)


/--
Given a hierarchical name `field`, returns the fully resolved field access, the base struct name, and the last projection function.
-/
private partial def expandField (structName : Name) (field : Name) : MetaM (Name × Name) := do
  match field with
  | .num .. | .anonymous => throwError m!"Invalid configuration field"
  | .str .anonymous fieldName => expandFieldName structName (Name.mkSimple fieldName)
  | .str field' fieldName =>
    let (field', projFn) ← expandField structName field'
    let notStructure {α} : MetaM α := throwError "Field `{field'}` of structure `{.ofConstName structName}` is not a structure"
    let .const structName' _ := (← getConstInfo projFn).type.getForallBody | notStructure
    unless isStructure (← getEnv) structName' do notStructure
    let (field'', projFn) ← expandFieldName structName' (Name.mkSimple fieldName)
    return (field' ++ field'', projFn)

/-- Elaborates a tactic configuration. -/
def elabConfig (recover : Bool) (structName : Name) (items : Array ConfigItemView) : TermElabM Expr :=
  withoutModifyingStateWithInfoAndMessages <| withLCtx {} {} <| withSaveInfoContext do
    let mkStructInst (source? : Option Term) (fields : TSyntaxArray ``Parser.Term.structInstField) : TermElabM Term :=
      match source? with
      | some source => `({$source with $fields* : $(mkCIdent structName)})
      | none        => `({$fields* : $(mkCIdent structName)})
    let mut source? : Option Term := none
    let mut seenFields : NameSet := {}
    let mut fields : TSyntaxArray ``Parser.Term.structInstField := #[]
    for item in items do
      try
        let option := item.option.getId.eraseMacroScopes
        if option == `config then
          unless fields.isEmpty do
            -- Flush fields. Even though these values will not be used, we still want to elaborate them.
            source? ← mkStructInst source? fields
            seenFields := {}
            fields := #[]
          let valSrc ← withRef item.value `(($item.value : $(mkCIdent structName)))
          if let some source := source? then
            source? ← withRef item.value `({$valSrc, $source with : $(mkCIdent structName)})
          else
            source? := valSrc
        else
          addCompletionInfo <| CompletionInfo.fieldId item.option option {} structName
          let (path, projFn) ← withRef item.option <| expandField structName option
          if item.bool then
            -- Verify that the type is `Bool`
            unless (← getConstInfo projFn).type.bindingBody! == .const ``Bool [] do
              throwErrorAt item.ref m!"Option is not boolean-valued, so `({option} := ...)` syntax must be used"
          let value ←
            match item.value with
            | `(by $seq:tacticSeq) =>
              -- Special case: `(opt := by tacs)` uses the `tacs` syntax itself
              withRef item.value <| `(Unhygienic.run `(tacticSeq| $seq))
            | value => pure value
          if seenFields.contains path then
            -- Flush fields. There is a duplicate, but we still want to elaborate both.
            source? ← mkStructInst source? fields
            seenFields := {}
            fields := #[]
          fields := fields.push <| ← `(Parser.Term.structInstField|
            $(mkCIdentFrom item.option path (canonical := true)):ident := $value)
          seenFields := seenFields.insert path
      catch ex =>
        if recover then
          logException ex
        else
          throw ex
    let stx : Term ← mkStructInst source? fields
    let e ← Term.withSynthesize <| Term.elabTermEnsuringType stx (mkConst structName)
    let e ← instantiateMVars e
    if e.hasMVar then
      throwError "Failed to evaluate configuration, it contains metavariables{indentExpr e}"
    return e

namespace EvalConfig
/-!
Configuration evaluation happens very frequently, and our default method is to use `Meta.evalExpr'`
to turn the `Expr` representing the elaborated configuration into a run time value.

That means hitting the compiler very frequently. To avoid this, we make a best-effort custom evaluator
that recognizes configurations, using reduction if needed. If it comes across anything it does not recognize,
it aborts and we fall back to `Meta.evalExpr'`.

In the following evaluators, we do not validate expressions have the expected type.

These functions are similar to those in `Lean.Meta.LitValues`, but the evaluators here do reductions.
-/

/--
Evaluates `f` on both `e` and `whnf e`.
-/
@[inline] private def evalHelper {α : Type} (f : Expr → MetaM α) (e : Expr) : MetaM α := do
  try
    f e
  catch _ =>
    f (← whnf e)

/-- Recognizes a boolean constant. -/
def evalBool : Expr → MetaM Bool :=
  evalHelper fun e =>
    if e.isConstOf ``Bool.true then return true
    else if e.isConstOf ``Bool.false then return false
    else failure

/-- Recognizes a natural number constant. -/
def evalNat : Expr → MetaM Nat :=
  evalHelper fun e => (e.nat? <|> e.rawNatLit?).getM

/-- Recognizes an integer constant. -/
def evalInt : Expr → MetaM Int :=
  evalHelper fun e =>
    e.int?.getM <|> do
      if e.isAppOfArity ``Int.ofNat 1 then
        Int.ofNat <$> evalNat e.appArg!
      else if e.isAppOfArity ``Int.negSucc 1 then
        Int.negSucc <$> evalNat e.appArg!
      else
        failure

/-- If `e` is not a constant application of one of the given constants, put it into whnf. -/
def whnfHelper (e : Expr) (consts : List Name) : MetaM Expr := do
  if let .const c _ := e.getAppFn then
    if consts.contains c then
      return e
  whnf e

/-- Recognizes a list of constants, each recognized by `f`. -/
def evalList {α : Type} (f : Expr → MetaM α) (e : Expr) : MetaM (List α) := do
  let mut xsRev : List α := []
  let mut e := e
  repeat
    e ← whnfHelper e [``List.nil, ``List.cons]
    match_expr e with
    | List.nil _ => break
    | List.cons _ a as =>
      xsRev := (← f a) :: xsRev
      e := as
    | _ => failure
  return xsRev.reverse

/--
Recognizes an array of constants, each recognized by `f`.
-/
def evalArray {α : Type} (f : Expr → MetaM α) (e : Expr) : MetaM (Array α) := do
  let_expr Array.mk _ e' := (← whnf e) | failure
  List.toArray <$> evalList f e'

private def evalSuffix := `_evalForConfig

mutual
/--
Creates an evaluator for the inductive type, as a private declaration.
Only non-recursive types with no parameters or indices are supported right now;
this covers most tactic configurations.
-/
private partial def deriveEval (tyName : Name) : CommandElabM Name :=
  withoutExporting <| withFreshMacroScope do
    if isPrivateName tyName then
      throwError "For `{.ofConstName tyName}`: Deriving evaluators for private types is not supported"
    let evalName := mkPrivateName (← getEnv) (tyName ++ evalSuffix)
    if (← getEnv).contains evalName then
      -- An evaluator already exists
      return evalName
    let indVal ← getConstInfoInduct tyName
    if indVal.all.length > 1 || indVal.isNested || indVal.isRec then
      throwError "For `{.ofConstName tyName}`: Recursive, nested, and mutually recursive inductive types are not supported yet"
    if indVal.numParams > 0 || indVal.numIndices > 0 then
      throwError "For `{.ofConstName tyName}`: Parameters and indices are not supported yet"
    if indVal.levelParams.length > 0 then
      throwError "For `{.ofConstName tyName}`: Universe polymorphism is not supported"
    let mkCmd : TermElabM Command := do
      let mut alts : TSyntaxArray ``Parser.Term.matchAltExpr := #[]
      for ctor in indVal.ctors do
        let alt ← forallTelescopeReducing (← inferType (.const ctor [])) fun xs _ => do
          let xs' ← xs.mapM (fun x => do mkIdent <$> mkFreshUserName (← x.fvarId!.getUserName))
          let ctorPatt ← xs'.foldlM (init := ← ``(Expr.const $(quote ctor) _))
            fun p x' => ``(Expr.app $p $x')
          let vs : Array Term ← (xs.zip xs').mapM fun (x, x') => do
            let f ← deriveEvalFor (← inferType x)
            `($f $x')
          let vs' : Array Term ← vs.mapM fun v => `(← $v)
          let ctorVal ← `(return @$(mkCIdent ctor) $vs'*)
          `(Parser.Term.matchAltExpr| | $ctorPatt => $ctorVal )
        alts := alts.push alt
      alts := alts.push <| ← `(Parser.Term.matchAltExpr| | _ => failure)
      let evalId := mkIdent (rootNamespace ++ privateToUserName evalName)
      let evalType ← ``(Expr → MetaM $(mkCIdent tyName))
      let me ← `(match e with $alts:matchAlt*)
      `(command|
          private def $evalId : $evalType := fun e => do
            let e ← $(mkCIdent ``whnfHelper):ident e $(quote indVal.ctors)
            $me:term)
    let cmd ← liftTermElabM mkCmd
    elabCommand cmd
    return evalName

/--
Try to derive an evaluator for the given expression.
-/
private partial def deriveEvalFor (e : Expr) : TermElabM Term := do
  trace[Elab.tacticConfig] "deriving for {e}"
  let e ← whnf e
  match_expr e with
  | Nat => ``(evalNat)
  | Int => ``(evalInt)
  | Bool => ``(evalBool)
  | List t => let f ← deriveEvalFor t; ``(evalList $f)
  | Array t => let f ← deriveEvalFor t; ``(evalArray $f)
  | _ =>
    let .const tyName' [] ← whnf e | throwError "Cannot derive evaluator for non-constant{indentExpr e}"
    let f ← liftCommandElabM <| deriveEval tyName'
    return mkCIdent f

end

private def mkEval? (typeName : Name) : CommandElabM (Option Term) := do
  try pure <| some <| mkCIdent (← EvalConfig.deriveEval typeName)
  catch ex =>
    trace[Elab.tacticConfig] "Failed to create a custom evaluator for `{.ofConstName typeName}`. Error: {ex.toMessageData}"
    pure none

end EvalConfig

open scoped EvalConfig

section
-- We automatically disable the following option for `macro`s but the subsequent `def` both contains
-- a quotation and is called only by `macro`s, so we disable the option for it manually. Note that
-- we can't use `in` as it is parsed as a single command and so the option would not influence the
-- parser.
set_option internal.parseQuotWithCurrentStage false

private meta def mkConfigElaborator
    (doc? : Option (TSyntax ``Parser.Command.docComment)) (elabName type monadName : Ident)
    (adapt recover : Term) (eval? : Option Term) : MacroM (TSyntax `command) := do
  let empty ← withRef type `({ : $type})
  let mut evalExpr ← `(Meta.evalExpr' (safety := .unsafe) $type ``$type e)
  if let some ev := eval? then
    let ev' ← `(guard (!debug.Elab.tacticConfig.forceEval.get (← getOptions)) *> $ev e)
    evalExpr ← `($ev' <|> do trace[Elab.tacticConfig] "Using compiler to evaluate{indentExpr e}"; $evalExpr:term)
  `(unsafe def evalUnsafe (e : Expr) : TermElabM $type := do
      profileitM Exception "tactic configuration interpretation" (← getOptions) do
        ($evalExpr:term : MetaM $type)
    @[implemented_by evalUnsafe] opaque eval (e : Expr) : TermElabM $type
    $[$doc?:docComment]?
    def $elabName (optConfig : Syntax) : $monadName $type := $adapt do
      let recover := $recover
      let go : TermElabM $type := withRef optConfig do
        let items := mkConfigItemViews (getConfigItems optConfig)
        if items.isEmpty then
          return $empty
        unless (← getEnv).contains ``$type do
          throwError m!"Error evaluating configuration: Environment does not yet contain type {``$type}"
        recordExtraModUseFromDecl (isMeta := true) ``$type
        let c ← elabConfig recover ``$type items
        if c.hasSyntheticSorry then
          -- An error is already logged, return the default.
          return $empty
        if c.hasSorry then
          throwError m!"Configuration contains `sorry`"
        try
          let res ← eval c
          return res
        catch ex =>
          let msg := m!"Error evaluating configuration\n{indentD c}\n\nException: {ex.toMessageData}"
          if false then
            logError msg
            return $empty
          else
            throwError msg
      go)

end

open Parser Parser.Command

@[builtin_command_elab configElab]
def elabConfigElab : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``docComment) := TSyntax.mk <$> stx[0].getOptional?
  let elabName : Ident := ⟨stx[2]⟩
  let type : Ident := ⟨stx[3]⟩
  let typeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo type
  let eval? ← EvalConfig.mkEval? typeName
  elabCommand <| ← liftMacroM <| mkConfigElaborator doc? elabName type (mkCIdent ``TacticM) (mkCIdent ``id) (← `((← read).recover)) eval?

-- TODO(kmill): remove
/-!
`declare_config_elab elabName TypeName` declares a function `elabName : Syntax → TacticM TypeName`
that elaborates a tactic configuration.
The tactic configuration can be from `Lean.Parser.Tactic.optConfig` or `Lean.Parser.Tactic.config`,
and these can also be wrapped in null nodes (for example, from `(config)?`).

The elaborator responds to the current recovery state.

For defining elaborators for commands, use `declare_command_config_elab`.
-/
macro (name := configElab') (priority := low) doc?:(docComment)? "declare_config_elab" elabName:ident type:ident : command => do
  mkConfigElaborator doc? elabName type (mkCIdent ``TacticM) (mkCIdent ``id) (← `((← read).recover)) none

open Linter.MissingDocs in
@[builtin_missing_docs_handler Command.configElab, builtin_missing_docs_handler configElab']
private def checkConfigElab : SimpleHandler := mkSimpleHandler "config elab"

@[builtin_command_elab commandConfigElab]
def elabCommandConfigElab : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``docComment) := TSyntax.mk <$> stx[0].getOptional?
  let elabName : Ident := ⟨stx[2]⟩
  let type : Ident := ⟨stx[3]⟩
  let typeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo type
  let eval? ← EvalConfig.mkEval? typeName
  elabCommand <| ← liftMacroM <| mkConfigElaborator doc? elabName type (mkCIdent ``CommandElabM) (mkCIdent ``liftTermElabM) (mkCIdent ``true) eval?

-- TODO(kmill): remove
/-!
`declare_command_config_elab elabName TypeName` declares a function `elabName : Syntax → CommandElabM TypeName`
that elaborates a command configuration.
The configuration can be from `Lean.Parser.Tactic.optConfig` or `Lean.Parser.Tactic.config`,
and these can also be wrapped in null nodes (for example, from `(config)?`).

The elaborator has error recovery enabled.
-/
macro (name := commandConfigElab') (priority := low) doc?:(docComment)? "declare_command_config_elab" elabName:ident type:ident : command => do
  mkConfigElaborator doc? elabName type (mkCIdent ``CommandElabM) (mkCIdent ``liftTermElabM) (mkCIdent ``true) none

open Linter.MissingDocs in
@[builtin_missing_docs_handler Command.commandConfigElab, builtin_missing_docs_handler Elab.Tactic.commandConfigElab']
private def checkCommandConfigElab : SimpleHandler := mkSimpleHandler "config elab"

end Lean.Elab.Tactic
