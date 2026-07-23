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

/-- Expand a `def` carrying `require`/`ensures` clauses into the plain `def` plus a spec theorem
`@[spec] theorem f.spec : ⦃P⦄ f args ⦃fun b => Q⦄ := by vcgen [f] with finish`. -/
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
  -- Replace the contract-carrying value with its inner `declVal` so the `def` elaborates normally.
  let cleanDeclaration := stx.setArg 1 (decl.setArg 3 val[2])
  if requireStx.isNone && ensuresStx.isNone then
    return cleanDeclaration
  unless (← Macro.hasDecl ``Std.Internal.Do.Triple) do
    Macro.throwErrorAt (if requireStx.isNone then ensuresStx else requireStx)
      "`require`/`ensures` contracts elaborate to a `vcgen`-proved specification theorem; \
add `import Std.Internal.Do` and `import Std.Tactic.Do` to use them."
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
  let thm ← `(command|
    @[spec] theorem $specId $binders* : ⦃ $pre ⦄ $fId $args* ⦃ $post ⦄ := by
      vcgen [$fId:ident] with finish)
  return mkNullNode #[cleanDeclaration, thm]

end Lean.Elab.Tactic.Do
