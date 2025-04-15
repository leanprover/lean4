/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
prelude
import Init.Ext
import Lean.Meta.Tactic.Ext
import Lean.Elab.DeclarationRange
import Lean.Elab.Tactic.RCases
import Lean.Elab.Tactic.Repeat
import Lean.Elab.Tactic.BuiltinTactic
import Lean.Elab.Command
import Lean.Linter.Basic

/-!
# Implementation of the `@[ext]` attribute
-/

namespace Lean.Elab.Tactic.Ext
open Meta Term

/-!
### Meta code for creating ext theorems
-/

/--
Constructs the hypotheses for the structure extensionality theorem that
states that two structures are equal if their fields are equal.

Calls the continuation `k` with the list of parameters to the structure,
two structure variables `x` and `y`, and a list of pairs `(field, ty)`
where each `ty` is of the form `x.field = y.field` or `HEq x.field y.field`.

If `flat` parses to `true`, any fields inherited from parent structures
are treated as fields of the given structure type.
If it is `false`, then the behind-the-scenes encoding of inherited fields
is visible in the extensionality lemma.
-/
def withExtHyps (struct : Name) (flat : Bool)
    (k : Array Expr → (x y : Expr) → Array (Name × Expr) → MetaM α) : MetaM α := do
  unless isStructure (← getEnv) struct do throwError "not a structure: {struct}"
  let structC ← mkConstWithLevelParams struct
  forallTelescope (← inferType structC) fun params _ => do
  withNewBinderInfos (params.map (·.fvarId!, BinderInfo.implicit)) do
  withLocalDecl `x .implicit (mkAppN structC params) fun x => do
  withLocalDecl `y .implicit (mkAppN structC params) fun y => do
    let mut hyps := #[]
    let fields ← if flat then
      pure <| getStructureFieldsFlattened (← getEnv) struct (includeSubobjectFields := false)
    else
      pure <| getStructureFields (← getEnv) struct
    for field in fields do
      let x_f ← mkProjection x field
      let y_f ← mkProjection y field
      unless ← isProof x_f do
        hyps := hyps.push (field, ← mkEqHEq x_f y_f)
    k params x y hyps

/--
Creates the type of the extensionality theorem for the given structure,
returning `∀ {x y : Struct}, x.1 = y.1 → x.2 = y.2 → x = y`, for example.
-/
def mkExtType (structName : Name) (flat : Bool) : MetaM Expr := withLCtx {} {} do
  withExtHyps structName flat fun params x y hyps => do
    let ty := hyps.foldr (init := ← mkEq x y) fun (f, h) ty => .forallE f h ty .default
    mkForallFVars (params |>.push x |>.push y) ty

/--
Derives the type of the `iff` form of an ext theorem.
-/
def mkExtIffType (extThmName : Name) : MetaM Expr := withLCtx {} {} do
  forallTelescopeReducing (← getConstInfo extThmName).type fun args ty => do
    let failNotEq := throwError "expecting a theorem proving x = y, but instead it proves{indentD ty}"
    let some (_, x, y) := ty.eq? | failNotEq
    let some xIdx := args.findIdx? (· == x) | failNotEq
    let some yIdx := args.findIdx? (· == y) | failNotEq
    unless xIdx + 1 == yIdx do
      throwError "expecting {x} and {y} to be consecutive arguments"
    let startIdx := yIdx + 1
    let toRevert := args[startIdx:].toArray
    let fvars ← toRevert.foldlM (init := {}) (fun st e => return collectFVars st (← inferType e))
    for fvar in toRevert do
      unless ← Meta.isProof fvar do
        throwError "argument {fvar} is not a proof, which is not supported for arguments after {x} and {y}"
      if fvars.fvarSet.contains fvar.fvarId! then
        throwError "argument {fvar} is depended upon, which is not supported for arguments after {x} and {y}"
    let conj := mkAndN (← toRevert.mapM (inferType ·)).toList
    -- Make everything implicit except for inst implicits
    let mut newBis := #[]
    for fvar in args[0:startIdx] do
      if (← fvar.fvarId!.getBinderInfo) matches .default | .strictImplicit then
        newBis := newBis.push (fvar.fvarId!, .implicit)
    withNewBinderInfos newBis do
      mkForallFVars args[:startIdx] <| mkIff ty conj

/--
Ensures that the given structure has an ext theorem, without validating any pre-existing theorems.
Returns the name of the ext theorem.

See `Lean.Elab.Tactic.Ext.withExtHyps` for an explanation of the `flat` argument.
-/
def realizeExtTheorem (structName : Name) (flat : Bool) : Elab.Command.CommandElabM Name := do
  unless isStructure (← getEnv) structName do
    throwError "'{structName}' is not a structure"
  let extName := structName.mkStr "ext"
  unless (← getEnv).contains extName do
    try
      Elab.Command.liftTermElabM <| withoutErrToSorry <| withDeclName extName do
        let type ← mkExtType structName flat
        let pf ← withSynthesize do
          let indVal ← getConstInfoInduct structName
          let params := Array.replicate indVal.numParams (← `(_))
          Elab.Term.elabTermEnsuringType (expectedType? := type) (implicitLambda := false)
            -- introduce the params, do cases on 'x' and 'y', and then substitute each equation
            (← `(by intro $params* {..} {..}; intros; subst_eqs; rfl))
        let pf ← instantiateMVars pf
        if pf.hasMVar then throwError "(internal error) synthesized ext proof contains metavariables{indentD pf}"
        let info ← getConstInfo structName
        addDecl <| Declaration.thmDecl {
          name := extName
          type
          value := pf
          levelParams := info.levelParams
        }
        modifyEnv fun env => addProtected env extName
        addDeclarationRangesFromSyntax extName (← getRef)
    catch e =>
      throwError m!"\
        Failed to generate an 'ext' theorem for '{.ofConstName structName}': {e.toMessageData}"
  return extName

/--
Given an 'ext' theorem, ensures that there is an iff version of the theorem (if possible),
without validating any pre-existing theorems.
Returns the name of the 'ext_iff' theorem.
-/
def realizeExtIffTheorem (extName : Name) : Elab.Command.CommandElabM Name := do
  let extIffName : Name :=
    match extName with
    | .str n s => .str n (s ++ "_iff")
    | _ => .str extName "ext_iff"
  unless (← getEnv).contains extIffName do
    try
      let info ← getConstInfo extName
      Elab.Command.liftTermElabM <| withoutErrToSorry <| withDeclName extIffName do
        let type ← mkExtIffType extName
        let pf ← withSynthesize do
          Elab.Term.elabTermEnsuringType (expectedType? := type) <| ← `(by
            intros
            refine ⟨?_, ?_⟩
            · intro h; cases h; and_intros <;> (intros; first | rfl | simp | fail "Failed to prove converse of ext theorem")
            · intro; (repeat cases ‹_ ∧ _›); apply $(mkCIdent extName) <;> assumption)
        let pf ← instantiateMVars pf
        if pf.hasMVar then throwError "(internal error) synthesized ext_iff proof contains metavariables{indentD pf}"
        addDecl <| Declaration.thmDecl {
          name := extIffName
          type
          value := pf
          levelParams := info.levelParams
        }
        -- Only declarations in a namespace can be protected:
        unless extIffName.isAtomic do
          modifyEnv fun env => addProtected env extIffName
        addDeclarationRangesFromSyntax extIffName (← getRef)
    catch e =>
      throwError m!"\
        Failed to generate an 'ext_iff' theorem from '{.ofConstName extName}': {e.toMessageData}\n\
        \n\
        Try '@[ext (iff := false)]' to prevent generating an 'ext_iff' theorem."
  return extIffName


/-!
### Attribute
-/

abbrev extExtension := Meta.Ext.extExtension
abbrev getExtTheorems := Meta.Ext.getExtTheorems

builtin_initialize registerBuiltinAttribute {
  name := `ext
  descr := "Marks a theorem as an extensionality theorem"
  add := fun declName stx kind => MetaM.run' do
    let `(attr| ext $[(iff := false%$iffFalse?)]? $[(flat := false%$flatFalse?)]? $(prio)?) := stx
      | throwError "invalid syntax for 'ext' attribute"
    let iff := iffFalse?.isNone
    let flat := flatFalse?.isNone
    let mut declName := declName
    if isStructure (← getEnv) declName then
      declName ← liftCommandElabM <| withRef stx <| realizeExtTheorem declName flat
    else if let some stx := flatFalse? then
      throwErrorAt stx "unexpected 'flat' configuration on @[ext] theorem"
    -- Validate and add theorem to environment extension
    let declTy := (← getConstInfo declName).type
    let (_, _, declTy) ← withDefault <| forallMetaTelescopeReducing declTy
    let failNotEq := throwError "\
      @[ext] attribute only applies to structures and to theorems proving 'x = y' where 'x' and 'y' are variables, \
      but this theorem proves{indentD declTy}"
    let some (ty, lhs, rhs) := declTy.eq? | failNotEq
    unless lhs.isMVar && rhs.isMVar do failNotEq
    let keys ← withReducible <| DiscrTree.mkPath ty
    let priority ← liftCommandElabM <| Elab.liftMacroM do evalPrio (prio.getD (← `(prio| default)))
    extExtension.add {declName, keys, priority} kind
    -- Realize iff theorem
    if iff then
      discard <| liftCommandElabM <| withRef stx <| realizeExtIffTheorem declName
  erase := fun declName => do
    let s := extExtension.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => extExtension.modifyState env fun _ => s
}


/-!
### Implementation of `ext` tactic
-/

/-- Apply a single extensionality theorem to `goal`. -/
def applyExtTheoremAt (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let tgt ← goal.getType'
  unless tgt.isAppOfArity ``Eq 3 do
    throwError "applyExtTheorem only applies to equations, not{indentExpr tgt}"
  let ty := tgt.getArg! 0
  let s ← saveState
  for lem in ← getExtTheorems ty do
    try
      -- Note: We have to do this extra check to ensure that we don't apply e.g.
      -- funext to a goal `(?a₁ : ?b) = ?a₂` to produce `(?a₁ x : ?b') = ?a₂ x`,
      -- since this will loop.
      -- We require that the type of the equality is not changed by the `goal.apply c` line
      -- TODO: add flag to apply tactic to toggle unification vs. matching
      withNewMCtxDepth do
        let c ← mkConstWithFreshMVarLevels lem.declName
        let (_, _, declTy) ← withDefault <| forallMetaTelescopeReducing (← inferType c)
        guard (← isDefEq tgt declTy)
      -- We use `newGoals := .all` as this is
      -- more useful in practice with dependently typed arguments of `@[ext]` theorems.
      return ← goal.apply (cfg := { newGoals := .all }) (← mkConstWithFreshMVarLevels lem.declName)
    catch _ => s.restore
  throwError "no applicable extensionality theorem found for{indentExpr ty}"

/-- Apply a single extensionality theorem to the current goal. -/
@[builtin_tactic applyExtTheorem] def evalApplyExtTheorem : Tactic := fun _ => do
  liftMetaTactic applyExtTheoremAt

/--
Postprocessor for `withExt` which runs `rintro` with the given patterns when the target is a
pi type.
-/
def tryIntros [Monad m] [MonadLiftT TermElabM m] (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (k : MVarId → List (TSyntax `rcasesPat) → m Nat) : m Nat := do
  match pats with
  | [] => k (← (g.intros : TermElabM _)).2 []
  | p::ps =>
    if (← (g.withContext g.getType' : TermElabM _)).isForall then
      let mut n := 0
      for g in ← RCases.rintro #[p] none g do
        n := n.max (← tryIntros g ps k)
      pure (n + 1)
    else k g pats

/--
Applies a single extensionality theorem, using `pats` to introduce variables in the result.
Runs continuation `k` on each subgoal.
-/
def withExt1 [Monad m] [MonadLiftT TermElabM m] (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (k : MVarId → List (TSyntax `rcasesPat) → m Nat) : m Nat := do
  let mut n := 0
  for g in ← (applyExtTheoremAt g : TermElabM _) do
    n := n.max (← tryIntros g pats k)
  pure n

/--
Applies extensionality theorems recursively, using `pats` to introduce variables in the result.
Runs continuation `k` on each subgoal.
-/
def withExtN [Monad m] [MonadLiftT TermElabM m] [MonadExcept Exception m]
    (g : MVarId) (pats : List (TSyntax `rcasesPat)) (k : MVarId → List (TSyntax `rcasesPat) → m Nat)
    (depth := 100) (failIfUnchanged := true) : m Nat :=
  match depth with
  | 0 => k g pats
  | depth+1 => do
    if failIfUnchanged then
      withExt1 g pats fun g pats => withExtN g pats k depth (failIfUnchanged := false)
    else try
      withExt1 g pats fun g pats => withExtN g pats k depth (failIfUnchanged := false)
    catch _ => k g pats

/--
Apply extensionality theorems as much as possible, using `pats` to introduce the variables
in extensionality theorems like `funext`. Returns a list of subgoals.

This is built on top of `withExtN`, running in `TermElabM` to build the list of new subgoals.
(And, for each goal, the patterns consumed.)
-/
def extCore (g : MVarId) (pats : List (TSyntax `rcasesPat))
    (depth := 100) (failIfUnchanged := true) :
    TermElabM (Nat × Array (MVarId × List (TSyntax `rcasesPat))) := do
  StateT.run (m := TermElabM) (s := #[])
    (withExtN g pats (fun g qs => modify (·.push (g, qs)) *> pure 0) depth failIfUnchanged)

@[builtin_tactic ext] def evalExt : Tactic := fun stx => do
  match stx with
  | `(tactic| ext $pats* $[: $n]?) => do
    let pats := RCases.expandRIntroPats pats
    let depth := n.map (·.getNat) |>.getD 100
    let (used, gs) ← extCore (← getMainGoal) pats.toList depth
    if RCases.linter.unusedRCasesPattern.get (← getOptions) then
      if used < pats.size then
        Linter.logLint RCases.linter.unusedRCasesPattern (mkNullNode pats[used:].toArray)
          m!"`ext` did not consume the patterns: {pats[used:]}"
    replaceMainGoal <| gs.map (·.1) |>.toList
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Ext
