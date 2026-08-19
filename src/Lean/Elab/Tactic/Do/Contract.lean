/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Std.Internal.Do
public import Lean.Elab.Util
public import Lean.Elab.Command
public import Lean.Elab.Do.Basic
import Lean.DocString.Extension
meta import Lean.Parser.Command
meta import Lean.Parser.Term
meta import Lean.Parser.Do
import Init.Syntax
import Init.Grind.Interactive

/-!
# Intrinsic verification syntax

A definition carrying `requires P` / `ensures b => Q` clauses expands to the plain definition plus a
`vcgen`-proven, `@[spec]`-tagged specification theorem `f.spec`. An `assert` element in a `do` block
elaborates to the assertion gadget that `vcgen` proves in the course of that theorem.
-/

public section

open Lean Lean.Parser.Command Std.Internal.Do Lean.Order

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

/-- Expand a `def` carrying `requires`/`ensures` clauses into the plain `def` plus a spec theorem
`@[spec] theorem f.spec : ⦃P⦄ f args ⦃fun b => Q⦄` proved by `vcgen`. A
`where finally | spec => steps` section supplies `grind`-mode steps for the verification
conditions `finish` leaves open. -/
@[builtin_macro Lean.Parser.Command.declaration]
def expandDefContract : Macro := fun stx => do
  let decl := stx[1]
  unless decl.isOfKind ``Lean.Parser.Command.definition do Macro.throwUnsupported
  -- `definition = "def "(0) >> declId(1) >> optDeclSig(2) >> (declVal <|> contractDeclVal)(3) >> …`
  -- `contractDeclVal = optional requiresClause(0) >> optional ensuresClause(1) >> declVal(2)`
  let val := decl[3]
  unless val.isOfKind ``Lean.Parser.Command.contractDeclVal do Macro.throwUnsupported
  let requiresStx := val[0]
  let ensuresStx := val[1]
  -- Replace the contract-carrying value with its inner `declVal` so the `def` elaborates normally.
  if requiresStx.isNone && ensuresStx.isNone then
    return stx.setArg 1 (decl.setArg 3 val[2])
  let (specStep?, strippedVal) ← extractSpecSection val[2]
  let cleanDeclaration := stx.setArg 1 (decl.setArg 3 strippedVal)
  unless (← Macro.hasDecl ``Std.Internal.Do.Triple) do
    Macro.throwErrorAt (if requiresStx.isNone then ensuresStx else requiresStx)
      "`requires`/`ensures` contracts elaborate to a `vcgen`-proved specification theorem; \
add `import Std.Internal.Do` to use them."
  let sig := decl[2]
  let fId : Ident := ⟨decl[1][0]⟩
  let specId := mkIdentFrom fId (fId.getId ++ `spec)
  let sigBinders := sig[0].getArgs
  let binders : TSyntaxArray [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder] :=
    sigBinders.map (⟨·⟩)
  let args := sigBinders.flatMap contractBinderIdents
  let pre : Term ← if requiresStx.isNone then `(⊤) else
    match requiresStx[0] with
    | `(requiresClause| requires $f:basicFun) => `(fun $f:basicFun)
    | `(requiresClause| requires $p:term) => pure p
    | _ => Macro.throwUnsupported
  let post : Term ← if ensuresStx.isNone then `(fun _ => ⊤) else
    match ensuresStx[0] with
    | `(ensuresClause| ensures $f:basicFun) => `(fun $f:basicFun)
    | `(ensuresClause| ensures $alts:matchAlts) => `(fun $alts:matchAlts)
    | _ => Macro.throwUnsupported
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
  -- `open scoped` activates the instances of `Std.Internal.Do` and the `⊤` notation of
  -- `Lean.Order` for the spec theorem without adding names to the user's scope.
  let thm ← `(command|
    open scoped Std.Internal.Do Lean.Order in
    @[spec] theorem $specId $binders* : ⦃ $pre ⦄ $fId $args* ⦃ $post ⦄ := by
      vcgen [$fId:ident] with (try finish)
      $specTac:tactic
      first
      | done
      | fail $msg)
  return mkNullNode #[mkContractNotice val, cleanDeclaration, thm]

open Lean.Elab.Do in
/-- Report the experimental status of each contract clause the notice carries. -/
@[builtin_command_elab Lean.Parser.Command.contractDeclVal]
def elabContractNotice : Elab.Command.CommandElab := fun stx => do
  for clause in stx.getArgs.pop do
    unless clause.isNone do
      let kw := clause[0][0]
      warnIntrinsicExperimental kw m!"`{kw.getAtomVal}` clause"

open Lean.Elab.Do Lean.Parser.Term in
@[builtin_doElem_elab Lean.Parser.Term.doAssertion]
def elabDoAssertion : DoElab := fun stx dec => do
  let tk := stx.raw[0]
  let as : Term ← match stx with
    | `(doAssertion| assert $f:basicFun) => `(fun $f:basicFun)
    | `(doAssertion| assert $p:term) => pure p
    | _ => throwUnsupportedSyntax
  unless (← getEnv).contains ``assertGadget do
    throwErrorAt tk
      "the `assert` element elaborates to a `vcgen` gadget; add `import Std.Internal.Do` to use it."
  warnIntrinsicExperimental tk m!"`assert` element"
  let dec ← dec.ensureUnitAt tk
  let e ← Term.elabTermEnsuringType (← `($(mkCIdent ``assertGadget) $as)) (← mkMonadApp (← mkPUnit))
  dec.mkBindUnlessPure e

end Lean.Elab.Tactic.Do
