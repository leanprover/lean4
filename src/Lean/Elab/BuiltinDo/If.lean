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
  let mγ ← mkMonadicType (← read).doBlockResultType
  let mi := (← read).monadInfo
  dec.withDuplicableCont fun dec => do
  elabNestedActions cond fun cond => do
  match cond with
  | `(doIfCond|$cond) =>
    let cond ← Term.elabTermEnsuringType cond (mkSort .zero)
    let then_ ← elabDoSeq thenSeq dec
    let else_ ← elabDoSeq elseSeq dec
    -- We resolve the instance only here so that we see more error messages when `cond` is a `sorry`
    let decidable ← Term.mkInstMVar (mkApp (mkConst ``Decidable) cond)
    return mkApp5 (mkConst ``ite [mi.v.succ]) mγ cond decidable then_ else_
  | `(doIfCond|_ : $cond) =>
    let cond ← Term.elabTermEnsuringType cond (mkSort .zero)
    let then_ ← withLocalDeclD (← mkFreshUserName `h) cond fun h => do
      mkLambdaFVars #[h] (← elabDoSeq thenSeq dec)
    let else_ ← withLocalDeclD (← mkFreshUserName `h) (mkApp (mkConst ``Not) cond) fun h => do
      mkLambdaFVars #[h] (← elabDoSeq elseSeq dec)
    let decidable ← Term.mkInstMVar (mkApp (mkConst ``Decidable) cond)
    return mkApp5 (mkConst ``dite [mi.v.succ]) mγ cond decidable then_ else_
  | `(doIfCond|$h:ident : $cond) =>
    let cond ← Term.elabTermEnsuringType cond (mkSort .zero)
    let then_ ← withLocalDeclD h.getId cond fun h => do
      mkLambdaFVars #[h] (← elabDoSeq thenSeq dec)
    let else_ ← withLocalDeclD h.getId (mkApp (mkConst ``Not) cond) fun h => do
      mkLambdaFVars #[h] (← elabDoSeq elseSeq dec)
    let decidable ← Term.mkInstMVar (mkApp (mkConst ``Decidable) cond)
    return mkApp5 (mkConst ``dite [mi.v.succ]) mγ cond decidable then_ else_
  | _ => throwUnsupportedSyntax
