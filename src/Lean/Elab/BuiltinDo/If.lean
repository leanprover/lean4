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
  match cond with
  | `(doIfCond|$cond) => elabIte cond thenSeq elseSeq dec
  | `(doIfCond|$h : $cond) => elabDite h cond thenSeq elseSeq dec
  | _ => throwUnsupportedSyntax
where
  elabIte cond thenSeq elseSeq dec := do
    -- It turned out to be far more reliable to offload as much work as possible to the App
    -- elaborator. However, for Lake.Package.mkBuildArchiveFacetConfig, we still need to postpone.
    doElabToSyntax "then branch of if with condition {cond}" (elabDoSeq thenSeq dec) fun then_ => do
    doElabToSyntax "else branch of if with condition {cond}" (elabDoSeq elseSeq dec) fun else_ => do
    let mγ ← mkMonadicType (← read).doBlockResultType
    Term.elabTermEnsuringType (← `(if $cond then $then_ else $else_)) mγ

  elabDite h cond thenSeq elseSeq dec := do
    -- It turned out to be far more reliable to offload as much work as possible to the App
    -- elaborator. However, for Lake.Package.mkBuildArchiveFacetConfig, we still need to postpone.
    -- let h ← h?.getDM (mkFreshUserName `h)
    let elabDiteBranch (then_ : Bool) : DoElabM Expr := do
      -- Term.tryPostponeIfNoneOrMVar ty?
      -- let some ty ← pure ty? | throwError "expected type must be known"
      -- let .forallE _ (.forallE _ cond _ _) _ _ := ty
      --   | Term.tryPostpone
      --     throwError "Internal error of `do` `dite` elaborator: expected a type of the form `(c → α) → (¬c → α) → α` but got {ty}"
      -- withLocalDeclD h (if then_ then cond else mkNot cond) fun h => do
      --   mkLambdaFVars #[h] (← elabDoSeq (if then_ then thenSeq else elseSeq) dec)
      elabDoSeq (if then_ then thenSeq else elseSeq) dec
    doElabToSyntax "then branch of if with condition {cond}" (elabDiteBranch true) fun then_ => do
    doElabToSyntax "else branch of if with condition {cond}" (elabDiteBranch false) fun else_ => do
    let mγ ← mkMonadicType (← read).doBlockResultType
    match h with
    | `(_%$tk) => Term.elabTermEnsuringType (← `(if $(⟨tk⟩):hole : $cond then $then_ else $else_)) mγ
    | `($h:ident) => Term.elabTermEnsuringType (← `(if $h:ident : $cond then $then_ else $else_)) mγ
    | _ => throwUnsupportedSyntax
