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
import Lean.DocString.Extension
meta import Lean.Parser.Command
meta import Lean.Parser.Term
import Init.Syntax
import Init.Grind.Interactive

/-!
# `require`/`ensures` contracts on `def`

A definition carrying `require P` / `ensures b => Q` clauses expands to the plain definition plus a
`vcgen`-proven, `@[spec]`-tagged specification theorem `f.spec`.
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

/-- The path from a `declVal` alternative to its `optional whereDecls` child. -/
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

/-- Extracts the grind-mode steps of a `where finally | spec => steps` section from a `declVal`
alternative, returning the steps and the `declVal` with the section removed. -/
private def extractSpecSection (v : Syntax) : MacroM (Option Syntax × Syntax) := do
  let some path := whereDeclsPath? v | return (none, v)
  let optWd := getPath v path
  if optWd.isNone then return (none, v)
  -- `whereDecls = "where"(0) >> letRecDecls(1) >> optional whereFinally(2)`
  -- `whereFinally = "finally"(0) >> optional tacticSeq(1) >> subsections(2)`
  let wd := optWd[0]
  let optWf := wd[2]
  if optWf.isNone then return (none, v)
  let wf := optWf[0]
  let (specs, others) := wf[2].getArgs.partition (·.isOfKind ``Lean.Parser.Term.whereFinallySpecSubsection)
  if specs.isEmpty then return (none, v)
  if h : 1 < specs.size then
    Macro.throwErrorAt specs[1] "duplicate `spec` section"
  -- `whereFinallySpecSubsection = "| "(0) >> "spec"(1) >> "=>"(2) >> sepBy1Indent grind(3)`
  let wf' := wf.setArg 2 (mkNullNode others)
  return (some specs[0]![3], setPath v path (mkNullNode #[wd.setArg 2 (mkNullNode #[wf'])]))

/-- Expand a `def` carrying `require`/`ensures` clauses into the plain `def` plus a spec theorem
`@[spec] theorem f.spec : ⦃P⦄ f args ⦃fun b => Q⦄` proved by `vcgen`. A
`where finally | spec => step` section supplies a `grind`-mode step for the verification
conditions `finish` leaves open. -/
@[builtin_macro Lean.Parser.Command.declaration]
def expandDefContract : Macro := fun stx => do
  let decl := stx[1]
  unless decl.isOfKind ``Lean.Parser.Command.definition do Macro.throwUnsupported
  -- `definition = "def "(0) >> declId(1) >> optDeclSig(2) >> (declVal <|> contractDeclVal)(3) >> …`
  -- `contractDeclVal = optional requireClause(0) >> optional ensuresClause(1) >> declVal(2)`
  let val := decl[3]
  unless val.isOfKind ``Lean.Parser.Command.contractDeclVal do Macro.throwUnsupported
  let requireStx := val[0]
  let ensuresStx := val[1]
  let (specStep?, strippedVal) ← extractSpecSection val[2]
  -- Replace the contract-carrying value with its inner `declVal` so the `def` elaborates normally.
  let cleanDeclaration := stx.setArg 1 (decl.setArg 3 strippedVal)
  if requireStx.isNone && ensuresStx.isNone then
    return cleanDeclaration
  unless (← Macro.hasDecl ``Std.Internal.Do.Triple) do
    Macro.throwErrorAt (if requireStx.isNone then ensuresStx else requireStx)
      "`require`/`ensures` contracts elaborate to a `vcgen`-proved specification theorem; \
add `import Std.Internal.Do` to use them."
  let sig := decl[2]
  let fId : Ident := ⟨decl[1][0]⟩
  let specId := mkIdentFrom fId (fId.getId ++ `spec)
  let sigBinders := sig[0].getArgs
  let binders : TSyntaxArray [`ident, ``Lean.Parser.Term.hole, ``Lean.Parser.Term.bracketedBinder] :=
    sigBinders.map (⟨·⟩)
  let args := sigBinders.flatMap contractBinderIdents
  let pre : Term ← if requireStx.isNone then `(⊤) else
    match requireStx[0] with
    | `(requireClause| require $p) => pure p
    | _ => Macro.throwUnsupported
  let post : Term ← if ensuresStx.isNone then `(fun _ => ⊤) else
    match ensuresStx[0] with
    | `(ensuresClause| ensures $bs* => $q) => `(fun $bs* => $q)
    | _ => Macro.throwUnsupported
  let msg : TSyntax `str := ⟨Syntax.mkStrLit <|
    if specStep?.isSome then
      s!"unproved verification condition for the contract of `{fId.getId}`; \
the `where finally | spec => ...` section does not discharge it"
    else
      s!"unproved verification condition for the contract of `{fId.getId}`; \
discharge it in a `where finally | spec => ...` section of the definition"⟩
  -- The discharger tries `finish`, then the section's steps, then `skip` on each verification
  -- condition, so conditions the steps do not close flow out of `vcgen`; the trailing `first`
  -- reports them in one aggregate error.
  let toStep (g : Syntax) : TSyntax ``Lean.Parser.Tactic.Grind.grindStep :=
    ⟨mkNode ``Lean.Parser.Tactic.Grind.grindStep #[g, mkNullNode]⟩
  let steps ← match specStep? with
    | some seq => do
        let mut arr := #[]
        for h : i in [0:seq.getArgs.size] do
          if i % 2 == 0 then
            arr := arr.push (toStep seq.getArgs[i])
        pure arr
    | none => do pure #[toStep (← `(grind| done))]
  -- `open scoped` activates `Std.Internal.Do`'s scoped instances for the spec theorem without
  -- adding names to the user's scope.
  let thm ← `(command|
    open scoped Std.Internal.Do in
    @[spec] theorem $specId $binders* : ⦃ $pre ⦄ $fId $args* ⦃ $post ⦄ := by
      vcgen [$fId:ident] with first (finish) ($[$steps];*) (skip)
      first
      | done
      | fail $msg)
  return mkNullNode #[cleanDeclaration, thm]

end Lean.Elab.Tactic.Do
