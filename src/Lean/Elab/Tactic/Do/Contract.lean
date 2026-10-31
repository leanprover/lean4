/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Std.WP
public import Lean.Elab.Util
public import Lean.Elab.Command
public import Lean.Elab.Do.Basic
import Lean.DocString.Extension
import Lean.Meta.Tactic.Simp.Main
meta import Lean.Parser.Command
meta import Lean.Parser.Term
meta import Lean.Parser.Do
import Init.Syntax
import Init.Grind.Interactive

/-!
# Intrinsic verification syntax

A definition carrying `given xs` / `requires P` / `ensures b => Q` / `throws e => R` clauses
expands to the plain definition plus a `vcgen`-proven, `@[spec]`-tagged specification theorem
`f.spec`. An `assert` element in a `do` block elaborates to the assertion gadget that `vcgen`
proves in the course of that theorem.
-/

public section

open Lean Lean.Parser.Command Std.WP Lean.Order

namespace Lean.Elab.Tactic.Do

/-- The identifiers bound by an explicit `(…)` binder, used to apply the definition in its spec. -/
def contractBinderIdents (binder : Syntax) : Array Ident :=
  match binder with
  | `(Lean.Parser.Term.bracketedBinderF| ($ids* $[: $_]? $(_annot?)?)) =>
      ids.filterMap fun b => if b.raw.isIdent then some ⟨b.raw⟩ else none
  | _ =>
      if binder.isIdent then #[⟨binder⟩] else #[]

/-- The path from a `declVal` alternative to its `optional whereDecls` child. `declValToWhereFinally`
in `Lean.Elab.MutualDef` walks the same indices to reach the section this one strips. -/
private def whereDeclsPath? (v : Syntax) : Option (List Nat) :=
  if v.isOfKind ``Lean.Parser.Command.declValSimple then some [3]
  else if v.isOfKind ``Lean.Parser.Command.whereStructInst then some [2]
  else if v.isOfKind ``Lean.Parser.Command.declValEqns then some [0, 2]
  else none

private def getPath (s : Syntax) : List Nat → Syntax
  | [] => s
  | i :: p => getPath s[i] p

private def setPath (s : Syntax) : List Nat → Syntax → Syntax
  | [], r => r
  | i :: p, r => s.setArg i (setPath s[i] p r)

/-- Extracts the tactics of a `where finally | spec => tacs` section from a `declVal` alternative,
returning them and the `declVal` with the section removed. -/
private def extractSpecSection (v : Syntax) : MacroM (Option Syntax × Syntax) := do
  let some path := whereDeclsPath? v | return (none, v)
  let optWd := getPath v path
  if optWd.isNone then return (none, v)
  -- `whereDecls = "where"(0) >> letRecDecls(1) >> optional whereFinally(2)`
  -- `whereFinally = "finally"(0) >> optional tacticSeq(1) >> subsections(2)`
  -- `whereFinallySubsection = "| "(0) >> ident(1) >> "=>"(2) >> tacticSeq(3)`
  let wd := optWd[0]
  let optWf := wd[2]
  if optWf.isNone then return (none, v)
  let wf := optWf[0]
  let (specs, others) := wf[2].getArgs.partition (·[1].getId.eraseMacroScopes == `spec)
  if specs.isEmpty then return (none, v)
  if h : 1 < specs.size then
    Macro.throwErrorAt specs[1] "duplicate `spec` section"
  let wf' := wf.setArg 2 (mkNullNode others)
  return (some specs[0]![3], setPath v path (mkNullNode #[wd.setArg 2 (mkNullNode #[wf'])]))

/-- The marker command carrying a `def`'s contract clauses to `elabContractNotice`, which reports
their experimental status from a monad that can read options and log. It reuses the
`contractDeclVal` kind, which is never itself a command, and drops the definition's value. -/
private def mkContractNotice (val : Syntax) : Syntax :=
  mkNode ``Lean.Parser.Command.contractDeclVal (val.getArgs.pop.push (mkNullNode #[]))

/-- Expand a `def` carrying `given`/`requires`/`ensures`/`throws` clauses into the plain `def`
plus a spec theorem `@[spec] theorem f.spec : ∀ xs, ⦃P⦄ f args ⦃fun b => Q; E⦄` proved by
`vcgen`. A `where finally | spec => steps` section supplies `grind`-mode steps for the
verification conditions `finish` leaves open. -/
@[builtin_macro Lean.Parser.Command.declaration]
def expandDefContract : Macro := fun stx => do
  let decl := stx[1]
  unless decl.isOfKind ``Lean.Parser.Command.definition do Macro.throwUnsupported
  -- `definition = "def "(0) >> declId(1) >> optDeclSig(2) >> (declVal <|> contractDeclVal)(3) >> …`
  -- `contractDeclVal = optional givenClause(0) >> optional requiresClause(1) >>
  --   optional ensuresClause(2) >> many throwsClause(3) >> declVal(4)`
  -- `givenClause = "given"(0) >> many1 binders(1)`
  let val := decl[3]
  unless val.isOfKind ``Lean.Parser.Command.contractDeclVal do Macro.throwUnsupported
  let givenStx := val[0]
  let requiresStx := val[1]
  let ensuresStx := val[2]
  let throwsStx := val[3]

  -- Error recovery on the declVal form might have instead parsed the decl as a contractDeclVal.
  -- If that is the case, we stop any attempt at expansion because it will just fail again in the
  -- `def` elaborator.
  if givenStx.isNone && requiresStx.isNone && ensuresStx.isNone && throwsStx.getNumArgs == 0 then
    Macro.throwUnsupported

  -- Construct `cleanDeclaration`, the regular, non-contract definition that the specification
  -- refers to. `cleanDeclaration` is elaborated by the usual `def` elaborator.
  let (specStep?, strippedVal) ← extractSpecSection val[4]
  let cleanDeclaration := stx.setArg 1 (decl.setArg 3 strippedVal)

  -- Contract def needs the proper Std.WP definitions to be imported.
  unless (← Macro.hasDecl ``Std.WP.Triple) do
    Macro.throwErrorAt
      (if !givenStx.isNone then givenStx else if !requiresStx.isNone then requiresStx
       else if !ensuresStx.isNone then ensuresStx else throwsStx)
      "`given`/`requires`/`ensures`/`throws` contracts elaborate to a `vcgen`-proved \
specification theorem; add `import Std.WP` to use them."

  let sig := decl[2]
  let fId : Ident := ⟨decl[1][0]⟩
  let specId := mkIdentFrom fId (fId.getId ++ `spec)
  let sigBinders := sig[0].getArgs
  -- `f.spec` quantifies the `given` binders but applies `f` to the signature's arguments alone.
  let givenBinders := if givenStx.isNone then #[] else givenStx[0][1].getArgs
  let binders : TSyntaxArray [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder] :=
    (sigBinders ++ givenBinders).map (⟨·⟩)
  let args := sigBinders.flatMap contractBinderIdents
  let pre : Term ← if requiresStx.isNone then `(⊤) else
    match requiresStx[0] with
    | `(requiresClause| requires $f:basicFun) => `(fun $f:basicFun)
    | `(requiresClause| requires $p:term) => pure p
    | _ => Macro.throwUnsupported
  let post : Term ← if ensuresStx.isNone then `(fun _ => ⊤) else
    match ensuresStx[0] with
    | `(ensuresClause| ensures $f:basicFun) => `(fun $f:basicFun)
    | _ => Macro.throwUnsupported
  -- Each `throws` clause fills the slot of its exception type; the remaining slots stay `⊥`.
  -- `contract_eposts%` unfolds the result in the stored statement, e.g. to an `estack⟨...⟩`.
  let triple : Term ← do
    let eposts : Term ← throwsStx.getArgs.foldrM (init := ← `(⊥))
      fun clause acc =>
        -- The clause's position carries over to its `set` application, so a failing slot
        -- instance reports at the clause.
        withRef clause do
          match clause with
          | `(throwsClause| throws $f:basicFun) =>
            `($(mkCIdent ``Std.WP.EPostSlot.set) (fun $f:basicFun) $acc)
          | _ => Macro.throwUnsupported
    -- Build the `contract_eposts%` node directly: the parser compiling this file predates it.
    let epostsGadget : Term :=
      ⟨mkNode `Lean.Parser.Term.contractEPosts #[mkAtom "contract_eposts%", eposts]⟩
    `(⦃ $pre ⦄ $fId $args* ⦃ $post; $epostsGadget ⦄)
  let msg : TSyntax `str := ⟨Syntax.mkStrLit <|
    if specStep?.isSome then
      s!"unproved verification conditions for the contract of `{fId.getId}`; \
the `where finally | spec => ...` section does not discharge them"
    else
      s!"unproved verification conditions for the contract of `{fId.getId}`; \
discharge them in a `where finally | spec => ...` section of the definition"⟩
  -- The section's tactics run on the verification conditions `finish` leaves open; the trailing
  -- `first` reports those that survive them.
  let specTac : TSyntax `tactic ← match specStep? with
    | some tacs => `(tactic| ($(⟨tacs⟩):tacticSeq))
    | none => `(tactic| skip)
  -- `open scoped` activates the instances of `Std.WP` and the `⊤` notation of
  -- `Lean.Order` for the spec theorem without adding names to the user's scope.
  let thm ← `(command|
    open scoped Std.WP Lean.Order in
    @[spec] theorem $specId $binders* : $triple := by
      vcgen [$fId:ident] with (try finish)
      $specTac:tactic
      first
      | done
      | fail $msg)
  return mkNullNode #[mkContractNotice val, cleanDeclaration, thm]

/-- Runs `Meta.simp` on `e` with exactly the lemmas in `names`. -/
private def simpOnlyWith (names : Array Name) (e : Expr) : Elab.TermElabM Expr := do
  let mut thms : Meta.SimpTheorems := {}
  for n in names do
    thms ← thms.addConst n
  let ctx ← Meta.Simp.mkContext (simpTheorems := #[thms])
    (congrTheorems := ← Meta.getSimpCongrTheorems)
  let (r, _) ← Meta.simp e ctx
  return r.expr

/-- Elaborating `contract_eposts% e` unfolds the `EPostSlot.set` applications and `⊥` in `e`, e.g.
to an `estack⟨...⟩` expression. Used in the expansion of `throws` clauses to yield simpler specs. -/
@[builtin_term_elab Lean.Parser.Term.contractEPosts]
def elabContractEPosts : Term.TermElab := fun stx expectedType? => do
  -- Wait for the type of the exception postconditions, so the slot instances resolve.
  Term.tryPostponeIfNoneOrMVar expectedType?
  if let some expectedType := expectedType? then
    if (← instantiateMVars expectedType).hasExprMVar then
      Term.tryPostpone
  let e ← Term.withSynthesize <| Term.elabTerm stx[1] expectedType?
  let e ← instantiateMVars e
  -- Unfold each `EPostSlot.set` to the body of its instance, e.g. `set R ⊥` to `(R, ⊥.snd)`.
  let e' ← Meta.transform e (post := fun e => do
    if e.isAppOf ``Std.WP.EPostSlot.set then
      if let some e' ← Meta.unfoldProjInst? e then return .visit e'
    return .continue)
  -- Without progress above, `e` is the bare `⊥` of a contract without `throws` clauses; keep it,
  -- so the spec prints in the short `⦃Q⦄` form. Otherwise rewrite the projections of `⊥`.
  if e' == e then
    return e
  simpOnlyWith #[``Lean.Order.Prod.fst_bot, ``Lean.Order.Prod.snd_bot, ``Std.WP.EStackEnd.bot_eq]
    e'

open Lean.Elab.Do in
/-- Report the experimental status of each contract clause the notice carries, in a slight
command-level misuse of a `contractDeclVal` node. Does not change the environment. -/
@[builtin_command_elab Lean.Parser.Command.contractDeclVal]
def elabContractNotice : Elab.Command.CommandElab := fun stx => do
  -- A group is the `optional` node of a `given`/`requires`/`ensures` clause or the `many` node
  -- of the `throws` clauses; each clause starts with its keyword atom.
  for group in stx.getArgs.pop do
    for clause in group.getArgs do
      let kw := clause[0]
      warnIntrinsicExperimental kw m!"`{kw.getAtomVal}` clause"

open Lean.Elab.Do Lean.Parser.Term in
@[builtin_doElem_elab Lean.Parser.Term.doAssertion]
def elabDoAssertion : DoElab := fun stx dec => do
  let tk := stx.raw[0]
  let as : Term ← match stx with
    | `(doAssertion| assert $f:basicFun) => `(fun $f:basicFun)
    | `(doAssertion| assert $p:term) => pure p
    | _ => throwUnsupportedSyntax
  unless (← getEnv).contains ``Gadget.assertGadget do
    throwErrorAt tk
      "the `assert` element elaborates to a `vcgen` gadget; add `import Std.WP` to use it."
  warnIntrinsicExperimental tk m!"`assert` element"
  let dec ← dec.ensureUnitAt tk
  -- `open scoped` activates the instances of `Std.WP` and the notation of `Lean.Order` for the
  -- assertion, as the contract's spec theorem does for the `requires` and `ensures` clauses.
  let e ← Term.elabTermEnsuringType
    (← `(open scoped Std.WP Lean.Order in $(mkCIdent ``Gadget.assertGadget) $as))
    (← mkMonadApp (← mkPUnit))
  dec.mkBindUnlessPure e

end Lean.Elab.Tactic.Do
