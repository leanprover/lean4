/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
import Lean.Elab.BuiltinDo.Basic

public section

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

/--
If the given syntax is a `doIf`, return an equivalent `doIf` that has an `else` but no `else if`s or
`if let`s.
-/
private def expandDoIf? (stx : Syntax) : MacroM (Option Syntax) := match stx with
  | `(doElem|if $_:doIfProp then $_ else $_) => pure none
  | `(doElem|if $cond:doIfCond then $t $[else if $conds:doIfCond then $ts]* $[else $e?]?) => withRef stx do
    let mut e : Syntax ← e?.getDM `(doSeq|pure PUnit.unit)
    let mut eIsSeq := true
    for (cond, t) in Array.zip (conds.reverse.push cond) (ts.reverse.push t) do
      e ← if eIsSeq then pure e else `(doSeq|$(⟨e⟩):doElem)
      e ← match cond with
        | `(doIfCond|let $pat := $d) => `(doElem| match $d:term with | $pat:term => $t | _ => $(⟨e⟩))
        | `(doIfCond|let $pat ← $d)  => `(doElem| match ← $d    with | $pat:term => $t | _ => $(⟨e⟩))
        | `(doIfCond|$cond:doIfProp) => `(doElem| if $cond:doIfProp then $t else $(⟨e⟩))
        | _                          => Macro.throwUnsupported
      eIsSeq := false
    return some e
  | _ => Macro.throwUnsupported

@[builtin_doElem_elab Lean.Parser.Term.doIf] def elabDoIf : DoElab := fun stx dec => do
  if let some stxNew ← liftMacroM <| expandDoIf? stx then
    return ← Term.withMacroExpansion stx stxNew <| elabDoElem ⟨stxNew⟩ dec
  let `(doIf|if $cond:doIfCond then $thenSeq else $elseSeq) := stx | throwUnsupportedSyntax
  dec.withDuplicableCont fun dec => do
  elabNestedActions cond fun cond => do
  match cond with
  | `(doIfCond|$cond) => elabIte cond thenSeq elseSeq dec
  | `(doIfCond|_ : $cond) => elabDite none cond thenSeq elseSeq dec
  | `(doIfCond|$h:ident : $cond) => elabDite (some h.getId) cond thenSeq elseSeq dec
  | _ => throwUnsupportedSyntax
where
  elabIte cond thenSeq elseSeq dec := do
    -- It turned out to be far more reliable to offload as much work as possible to the App
    -- elaborator.
    let mγ ← mkMonadicType (← read).doBlockResultType
    let then_ ← elabDoSeq thenSeq dec
    let else_ ← elabDoSeq elseSeq dec
    let then_ ← Term.exprToSyntax then_
    let else_ ← Term.exprToSyntax else_
    Term.elabTermEnsuringType (← `(ite $cond $then_ $else_)) mγ (catchExPostpone := false)

  elabDite h? cond thenSeq elseSeq dec := do
    -- It turned out to be far more reliable to offload as much work as possible to the App
    -- elaborator.
    let mγ ← mkMonadicType (← read).doBlockResultType
    let mγ ← Term.exprToSyntax mγ
    let dite ← Term.elabTerm (← `(@dite $mγ $cond _)) none (catchExPostpone := false)
    let ty ← inferType dite
    let cond ←
      match ← instantiateMVars ty with
      | .forallE _ (.forallE _ cond _ _) _ _ =>
        pure cond
      | _ =>
        Term.tryPostpone
        throwError "Internal error of `do` `dite` elaborator: expected a type of the form `(c → α) → (¬c → α) → α` but got {ty}"
    let h ← h?.getDM (mkFreshUserName `h)
    let then_ ← withLocalDeclD h cond fun h => do
      mkLambdaFVars #[h] (← elabDoSeq thenSeq dec)
    let else_ ← withLocalDeclD h (mkApp (mkConst ``Not) cond) fun h => do
      mkLambdaFVars #[h] (← elabDoSeq elseSeq dec)
    return mkApp2 dite then_ else_
