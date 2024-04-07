/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
prelude
import Init.Ext
import Lean.Elab.Tactic.RCases
import Lean.Elab.Tactic.Repeat
import Lean.Elab.Tactic.BuiltinTactic
import Lean.Elab.Command
import Lean.Linter.Util

namespace Lean.Elab.Tactic.Ext
open Meta Term
/-- Information about an extensionality theorem, stored in the environment extension. -/
structure ExtTheorem where
  /-- Declaration name of the extensionality theorem. -/
  declName : Name
  /-- Priority of the extensionality theorem. -/
  priority : Nat
  /--
  Key in the discrimination tree,
  for the type in which the extensionality theorem holds.
  -/
  keys : Array DiscrTree.Key
  deriving Inhabited, Repr, BEq, Hashable

/-- The state of the `ext` extension environment -/
structure ExtTheorems where
  /-- The tree of `ext` extensions. -/
  tree   : DiscrTree ExtTheorem := {}
  /-- Erased `ext`s via `attribute [-ext]`. -/
  erased  : PHashSet Name := {}
  deriving Inhabited

/-- Discrimation tree settings for the `ext` extension. -/
def extExt.config : WhnfCoreConfig := {}

/-- The environment extension to track `@[ext]` theorems. -/
builtin_initialize extExtension :
    SimpleScopedEnvExtension ExtTheorem ExtTheorems ←
  registerSimpleScopedEnvExtension {
    addEntry := fun { tree, erased } thm =>
      { tree := tree.insertCore thm.keys thm, erased := erased.erase thm.declName }
    initial := {}
  }

/-- Gets the list of `@[ext]` theorems corresponding to the key `ty`,
ordered from high priority to low. -/
@[inline] def getExtTheorems (ty : Expr) : MetaM (Array ExtTheorem) := do
  let extTheorems := extExtension.getState (← getEnv)
  let arr ← extTheorems.tree.getMatch ty extExt.config
  let erasedArr := arr.filter fun thm => !extTheorems.erased.contains thm.declName
  -- Using insertion sort because it is stable and the list of matches should be mostly sorted.
  -- Most ext theorems have default priority.
  return erasedArr.insertionSort (·.priority < ·.priority) |>.reverse

/--
Erases a name marked `ext` by adding it to the state's `erased` field and
removing it from the state's list of `Entry`s.

This is triggered by `attribute [-ext] name`.
-/
def ExtTheorems.eraseCore (d : ExtTheorems) (declName : Name) : ExtTheorems :=
 { d with erased := d.erased.insert declName }

/--
  Erases a name marked as a `ext` attribute.
  Check that it does in fact have the `ext` attribute by making sure it names a `ExtTheorem`
  found somewhere in the state's tree, and is not erased.
-/
def ExtTheorems.erase [Monad m] [MonadError m] (d : ExtTheorems) (declName : Name) :
    m ExtTheorems := do
  unless d.tree.containsValueP (·.declName == declName) && !d.erased.contains declName do
    throwError "'{declName}' does not have [ext] attribute"
  return d.eraseCore declName

builtin_initialize registerBuiltinAttribute {
  name := `ext
  descr := "Marks a theorem as an extensionality theorem"
  add := fun declName stx kind => do
    let `(attr| ext $[(flat := $f)]? $(prio)?) := stx
      | throwError "unexpected @[ext] attribute {stx}"
    if isStructure (← getEnv) declName then
      liftCommandElabM <| Elab.Command.elabCommand <|
        ← `(declare_ext_theorems_for $[(flat := $f)]? $(mkCIdentFrom stx declName) $[$prio]?)
    else MetaM.run' do
      if let some flat := f then
        throwErrorAt flat "unexpected 'flat' config on @[ext] theorem"
      let declTy := (← getConstInfo declName).type
      let (_, _, declTy) ← withDefault <| forallMetaTelescopeReducing declTy
      let failNotEq := throwError
        "@[ext] attribute only applies to structures or theorems proving x = y, got {declTy}"
      let some (ty, lhs, rhs) := declTy.eq? | failNotEq
      unless lhs.isMVar && rhs.isMVar do failNotEq
      let keys ← withReducible <| DiscrTree.mkPath ty extExt.config
      let priority ← liftCommandElabM do Elab.liftMacroM do
        evalPrio (prio.getD (← `(prio| default)))
      extExtension.add {declName, keys, priority} kind
  erase := fun declName => do
    let s := extExtension.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => extExtension.modifyState env fun _ => s
}

/--
Constructs the hypotheses for the structure extensionality theorem that
states that two structures are equal if their fields are equal.

Calls the continuation `k` with the list of parameters to the structure,
two structure variables `x` and `y`, and a list of pairs `(field, ty)`
where `ty` is `x.field = y.field` or `HEq x.field y.field`.

If `flat` parses to `true`, any fields inherited from parent structures
are treated fields of the given structure type.
If it is `false`, then the behind-the-scenes encoding of inherited fields
is visible in the extensionality lemma.
-/
-- TODO: this is probably the wrong place to have this function
def withExtHyps (struct : Name) (flat : Term)
    (k : Array Expr → (x y : Expr) → Array (Name × Expr) → MetaM α) : MetaM α := do
  let flat ← match flat with
  | `(true) => pure true
  | `(false) => pure false
  | _ => throwErrorAt flat "expected 'true' or 'false'"
  unless isStructure (← getEnv) struct do throwError "not a structure: {struct}"
  let structC ← mkConstWithLevelParams struct
  forallTelescope (← inferType structC) fun params _ => do
  withNewBinderInfos (params.map (·.fvarId!, BinderInfo.implicit)) do
  withLocalDeclD `x (mkAppN structC params) fun x => do
  withLocalDeclD `y (mkAppN structC params) fun y => do
    let mut hyps := #[]
    let fields ← if flat then
      pure <| getStructureFieldsFlattened (← getEnv) struct (includeSubobjectFields := false)
    else
      pure <| getStructureFields (← getEnv) struct
    for field in fields do
      let x_f ← mkProjection x field
      let y_f ← mkProjection y field
      if ← isProof x_f then
        pure ()
      else if ← isDefEq (← inferType x_f) (← inferType y_f) then
        hyps := hyps.push (field, ← mkEq x_f y_f)
      else
        hyps := hyps.push (field, ← mkHEq x_f y_f)
    k params x y hyps

/--
Creates the type of the extensionality theorem for the given structure,
elaborating to `x.1 = y.1 → x.2 = y.2 → x = y`, for example.
-/
@[builtin_term_elab extType] def elabExtType : TermElab := fun stx _ => do
  match stx with
  | `(ext_type%  $flat:term $struct:ident) => do
    withExtHyps (← realizeGlobalConstNoOverloadWithInfo struct) flat fun params x y hyps => do
      let ty := hyps.foldr (init := ← mkEq x y) fun (f, h) ty =>
        mkForall f BinderInfo.default h ty
      mkForallFVars (params |>.push x |>.push y) ty
  | _ => throwUnsupportedSyntax

/--
Creates the type of the iff-variant of the extensionality theorem for the given structure,
elaborating to `x = y ↔ x.1 = y.1 ∧ x.2 = y.2`, for example.
-/
@[builtin_term_elab extIffType] def elabExtIffType : TermElab := fun stx _ => do
  match stx with
  | `(ext_iff_type% $flat:term $struct:ident) => do
    withExtHyps (← realizeGlobalConstNoOverloadWithInfo struct) flat fun params x y hyps => do
      mkForallFVars (params |>.push x |>.push y) <|
        mkIff (← mkEq x y) <| mkAndN (hyps.map (·.2)).toList
  | _ => throwUnsupportedSyntax

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
    (depth := 1000000) (failIfUnchanged := true) : m Nat :=
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
    (depth := 1000000) (failIfUnchanged := true) :
    TermElabM (Nat × Array (MVarId × List (TSyntax `rcasesPat))) := do
  StateT.run (m := TermElabM) (s := #[])
    (withExtN g pats (fun g qs => modify (·.push (g, qs)) *> pure 0) depth failIfUnchanged)

@[builtin_tactic ext] def evalExt : Tactic := fun stx => do
  match stx with
  | `(tactic| ext $pats* $[: $n]?) => do
    let pats := RCases.expandRIntroPats pats
    let depth := n.map (·.getNat) |>.getD 1000000
    let (used, gs) ← extCore (← getMainGoal) pats.toList depth
    if RCases.linter.unusedRCasesPattern.get (← getOptions) then
      if used < pats.size then
        Linter.logLint RCases.linter.unusedRCasesPattern (mkNullNode pats[used:].toArray)
          m!"`ext` did not consume the patterns: {pats[used:]}"
    replaceMainGoal <| gs.map (·.1) |>.toList
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Ext
