/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Util.CollectAxioms
import Lean.Elab.Deriving.Basic
import Lean.Elab.MutualDef

/-!
# Implementation of `#eval` command
-/

namespace Lean.Elab.Command
open Meta

register_builtin_option eval.pp : Bool := {
  defValue := true
  descr    := "('#eval' command) enables using 'ToExpr' instances to pretty print the result, \
               otherwise uses 'Repr' or 'ToString' instances"
}

register_builtin_option eval.type : Bool := {
  defValue := false -- TODO: set to 'true'
  descr    := "('#eval' command) enables pretty printing the type of the result"
}

register_builtin_option eval.derive.repr : Bool := {
  defValue := true
  descr    := "('#eval' command) enables auto-deriving 'Repr' instances as a fallback"
}

builtin_initialize
  registerTraceClass `Elab.eval

/--
Elaborates the term, ensuring the result has no expression metavariables.
If there would be unsolved-for metavariables, tries hinting that the resulting type
is a monadic value with the `CommandElabM`, `TermElabM`, or `IO` monads.
Throws errors if the term is a proof or a type, but lifts props to `Bool` using `mkDecide`.
-/
private def elabTermForEval (term : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let ty ← expectedType?.getDM mkFreshTypeMVar
  let e ← Term.elabTermEnsuringType term ty
  synthesizeWithHinting ty
  let e ← instantiateMVars e
  if (← Term.logUnassignedUsingErrorInfos (← getMVars e)) then throwAbortTerm
  if ← isProof e then
    throwError m!"cannot evaluate, proofs are not computationally relevant"
  let e ← if (← isProp e) then mkDecide e else pure e
  if ← isType e then
    throwError m!"cannot evaluate, types are not computationally relevant"
  trace[Elab.eval] "elaborated term:{indentExpr e}"
  return e
where
  /-- Try different strategies to make `Term.synthesizeSyntheticMVarsNoPostponing` succeed. -/
  synthesizeWithHinting (ty : Expr) : TermElabM Unit := do
    Term.synthesizeSyntheticMVarsUsingDefault
    let s ← saveState
    try
      Term.synthesizeSyntheticMVarsNoPostponing
    catch ex =>
      let exS ← saveState
      -- Try hinting that `ty` is a monad application.
      for m in #[``CommandElabM, ``TermElabM, ``IO] do
        s.restore true
        try
          if ← isDefEq ty (← mkFreshMonadApp m) then
            Term.synthesizeSyntheticMVarsNoPostponing
            return
        catch _ => pure ()
      -- None of the hints worked, so throw the original error.
      exS.restore true
      throw ex
  mkFreshMonadApp (n : Name) : MetaM Expr := do
    let m ← mkConstWithFreshMVarLevels n
    let (args, _, _) ← forallMetaBoundedTelescope (← inferType m) 1
    return mkAppN m args

private def addAndCompileExprForEval (declName : Name) (value : Expr) (allowSorry := false) : TermElabM Unit := do
  -- Use the `elabMutualDef` machinery to be able to support `let rec`.
  -- Hack: since we are using the `TermElabM` version, we can insert the `value` as a metavariable via `exprToSyntax`.
  -- An alternative design would be to make `elabTermForEval` into a term elaborator and elaborate the command all at once
  -- with `unsafe def _eval := term_for_eval% $t`, which we did try, but unwanted error messages
  -- such as "failed to infer definition type" can surface.
  let defView := mkDefViewOfDef { isUnsafe := true }
    (← `(Parser.Command.definition|
          def $(mkIdent <| `_root_ ++ declName) := $(← Term.exprToSyntax value)))
  Term.elabMutualDef #[] { header := "" } #[defView]
  unless allowSorry do
    let axioms ← collectAxioms declName
    if axioms.contains ``sorryAx then
      throwError "\
        aborting evaluation since the expression depends on the 'sorry' axiom, \
        which can lead to runtime instability and crashes.\n\n\
        To attempt to evaluate anyway despite the risks, use the '#eval!' command."

/--
Try to make a `@projFn ty inst e` application, even if it takes unfolding the type `ty` of `e` to synthesize the instance `inst`.
-/
private partial def mkDeltaInstProj (inst projFn : Name) (e : Expr) (ty? : Option Expr := none) (tryReduce : Bool := true) : MetaM Expr := do
  let ty ← ty?.getDM (inferType e)
  if let .some inst ← trySynthInstance (← mkAppM inst #[ty]) then
    mkAppOptM projFn #[ty, inst, e]
  else
    let ty ← whnfCore ty
    let some ty ← unfoldDefinition? ty
      | guard tryReduce
        -- Reducing the type is a strategy `#eval` used before the refactor of #5627.
        -- The test lean/run/hlistOverload.lean depends on it, so we preserve the behavior.
        let ty ← reduce (skipTypes := false) ty
        mkDeltaInstProj inst projFn e ty (tryReduce := false)
    mkDeltaInstProj inst projFn e ty tryReduce

/-- Try to make a `toString e` application, even if it takes unfolding the type of `e` to find a `ToString` instance. -/
private def mkToString (e : Expr) (ty? : Option Expr := none) : MetaM Expr := do
  mkDeltaInstProj ``ToString ``toString e ty?

/-- Try to make a `repr e` application, even if it takes unfolding the type of `e` to find a `Repr` instance. -/
private def mkRepr (e : Expr) (ty? : Option Expr := none) : MetaM Expr := do
  mkDeltaInstProj ``Repr ``repr e ty?

/-- Try to make a `toExpr e` application, even if it takes unfolding the type of `e` to find a `ToExpr` instance. -/
private def mkToExpr (e : Expr) (ty? : Option Expr := none) : MetaM Expr := do
  mkDeltaInstProj ``ToExpr ``toExpr e ty?

/--
Returns a representation of `e` using `Format`, or else fails.
If the `eval.derive.repr` option is true, then tries automatically deriving a `Repr` instance first.
Currently auto-derivation does not attempt to derive recursively.
-/
private def mkFormat (e : Expr) : MetaM Expr := do
  mkRepr e <|> (do mkAppM ``Std.Format.text #[← mkToString e])
  <|> do
    if eval.derive.repr.get (← getOptions) then
      if let .const name _ := (← whnf (← inferType e)).getAppFn then
        try
          trace[Elab.eval] "Attempting to derive a 'Repr' instance for '{name}'"
          liftCommandElabM do applyDerivingHandlers ``Repr #[name] none
          resetSynthInstanceCache
          return ← mkRepr e
        catch ex =>
          trace[Elab.eval] "Failed to use derived 'Repr' instance. Exception: {ex.toMessageData}"
    throwError m!"could not synthesize a 'Repr' or 'ToString' instance for type{indentExpr (← inferType e)}"

/--
Returns a representation of `e` using `MessageData`, or else fails.
Tries `mkFormat` if a `ToExpr` instance can't be synthesized.
-/
private def mkMessageData (e : Expr) : MetaM Expr := do
  (do guard <| eval.pp.get (← getOptions); mkAppM ``MessageData.ofExpr #[← mkToExpr e])
  <|> (return mkApp (mkConst ``MessageData.ofFormat) (← mkFormat e))
  <|> do throwError m!"could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type{indentExpr (← inferType e)}"

private structure EvalAction where
  eval : CommandElabM MessageData
  /-- Whether to print the result of evaluation.
  If `some`, the expression is what type to use for the type ascription when `pp.type` is true. -/
  printVal : Option Expr

unsafe def elabEvalCoreUnsafe (bang : Bool) (tk term : Syntax) (expectedType? : Option Expr) : CommandElabM Unit := withRef tk do
  let declName := `_eval
  -- `t` is either `MessageData` or `Format`, and `mkT` is for synthesizing an expression that yields a `t`.
  -- The `toMessageData` function adapts `t` to `MessageData`.
  let mkAct {t : Type} [Inhabited t] (toMessageData : t → MessageData) (mkT : Expr → MetaM Expr) (e : Expr) : TermElabM EvalAction := do
    -- Create a monadic action given the name of the monad `mc`, the monad `m` itself,
    -- and an expression `e` to evaluate in this monad.
    -- A trick here is that `mkMAct?` makes use of `MonadEval` instances are currently available in this stage,
    -- and we do not need them to be available in the target environment.
    let mkMAct? (mc : Name) (m : Type → Type) [Monad m] [MonadEvalT m CommandElabM] (e : Expr) : TermElabM (Option EvalAction) := do
      let some e ← observing? (mkAppOptM ``MonadEvalT.monadEval #[none, mkConst mc, none, none, e])
        | return none
      let eType := e.appFn!.appArg!
      if ← isDefEq eType (mkConst ``Unit) then
        addAndCompileExprForEval declName e (allowSorry := bang)
        let mf : m Unit ← evalConst (m Unit) declName
        return some { eval := do MonadEvalT.monadEval mf; pure "", printVal := none }
      else
        let rf ← withLocalDeclD `x eType fun x => do mkLambdaFVars #[x] (← mkT x)
        let r ← mkAppM ``Functor.map #[rf, e]
        addAndCompileExprForEval declName r (allowSorry := bang)
        let mf : m t ← evalConst (m t) declName
        return some { eval := toMessageData <$> MonadEvalT.monadEval mf, printVal := some eType }
    if let some act ← mkMAct? ``CommandElabM CommandElabM e
                    -- Fallbacks in case we are in the Lean package but don't have `CommandElabM` yet
                    <||> mkMAct? ``TermElabM TermElabM e <||> mkMAct? ``MetaM MetaM e <||> mkMAct? ``CoreM CoreM e
                    -- Fallback in case nothing is imported
                    <||> mkMAct? ``IO IO e then
      return act
    else
      -- Otherwise, assume this is a pure value.
      -- There is no need to adapt pure values to `CommandElabM`.
      -- This enables `#eval` to work on pure values even when `CommandElabM` is not available.
      let r ← try mkT e catch ex => do
        -- Diagnose whether the value is monadic for a representable value, since it's better to mention `MonadEval` in that case.
        try
          let some (m, ty) ← isTypeApp? (← inferType e) | failure
          guard <| (← isMonad? m).isSome
          -- Verify that there is a way to form some representation:
          discard <| withLocalDeclD `x ty fun x => mkT x
        catch _ =>
          throw ex
        throwError m!"unable to synthesize '{``MonadEval}' instance \
          to adapt{indentExpr (← inferType e)}\n\
          to '{``IO}' or '{``CommandElabM}'."
      addAndCompileExprForEval declName r (allowSorry := bang)
      -- `evalConst` may emit IO, but this is collected by `withIsolatedStreams` below.
      let r ← toMessageData <$> evalConst t declName
      return { eval := pure r, printVal := some (← inferType e) }
  let (output, exOrRes) ← IO.FS.withIsolatedStreams do
    try
      -- Generate an action without executing it. We use `withoutModifyingEnv` to ensure
      -- we don't pollute the environment with auxiliary declarations.
      let act : EvalAction ← liftTermElabM do Term.withDeclName declName do withoutModifyingEnv do
        let e ← elabTermForEval term expectedType?
        -- If there is an elaboration error, don't evaluate!
        if e.hasSyntheticSorry then throwAbortTerm
        -- We want `#eval` to work even in the core library, so if `ofFormat` isn't available,
        -- we fall back on a `Format`-based approach.
        if (← getEnv).contains ``Lean.MessageData.ofFormat then
          mkAct id (mkMessageData ·) e
        else
          mkAct Lean.MessageData.ofFormat (mkFormat ·) e
      let res ← act.eval
      return Sum.inr (res, act.printVal)
    catch ex =>
      return Sum.inl ex
  if !output.isEmpty then logInfoAt tk output
  match exOrRes with
  | .inl ex => logException ex
  | .inr (_, none) => pure ()
  | .inr (res, some type) =>
    if eval.type.get (← getOptions) then
      logInfo m!"{res} : {type}"
    else
      logInfo res

@[implemented_by elabEvalCoreUnsafe]
opaque elabEvalCore (bang : Bool) (tk term : Syntax) (expectedType? : Option Expr) : CommandElabM Unit

@[builtin_command_elab «eval»]
def elabEval : CommandElab
  | `(#eval%$tk $term) => elabEvalCore false tk term none
  | _ => throwUnsupportedSyntax

@[builtin_command_elab evalBang]
def elabEvalBang : CommandElab
  | `(#eval!%$tk $term) => elabEvalCore true tk term none
  | _ => throwUnsupportedSyntax

@[builtin_command_elab runCmd]
def elabRunCmd : CommandElab
  | `(run_cmd%$tk $elems:doSeq) => do
    unless (← getEnv).contains ``CommandElabM do
      throwError "to use this command, include `import Lean.Elab.Command`"
    elabEvalCore false tk (← `(discard do $elems)) (mkApp (mkConst ``CommandElabM) (mkConst ``Unit))
  | _ => throwUnsupportedSyntax

@[builtin_command_elab runElab]
def elabRunElab : CommandElab
  | `(run_elab%$tk $elems:doSeq) => do
    unless (← getEnv).contains ``TermElabM do
      throwError "to use this command, include `import Lean.Elab.Term`"
    elabEvalCore false tk (← `(discard do $elems)) (mkApp (mkConst ``TermElabM) (mkConst ``Unit))
  | _ => throwUnsupportedSyntax

@[builtin_command_elab runMeta]
def elabRunMeta : CommandElab := fun stx =>
  match stx with
  | `(run_meta%$tk $elems:doSeq) => do
    unless (← getEnv).contains ``MetaM do
      throwError "to use this command, include `import Lean.Meta.Basic`"
    elabEvalCore false tk (← `(discard do $elems)) (mkApp (mkConst ``MetaM) (mkConst ``Unit))
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
