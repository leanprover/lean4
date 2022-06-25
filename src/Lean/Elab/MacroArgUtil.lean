/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Syntax

namespace Lean.Elab.Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

/- Convert `macro` arg into a `syntax` command item and a pattern element -/
partial def expandMacroArg (stx : TSyntax ``macroArg) : CommandElabM (TSyntax `stx × Term) := do
  let (id?, id, stx) ← match (← liftMacroM <| expandMacros stx) with
    | `(macroArg| $id:ident:$stx) => pure (some id, (id : Term), stx)
    | `(macroArg| $stx:stx)       => pure (none, (← `(x)), stx)
    | _                           => throwUnsupportedSyntax
  mkSyntaxAndPat id? id stx
where
  mkSyntaxAndPat id? id stx := do
    let pat ← match stx with
    | `(stx| $s:str)         => pure ⟨mkNode `token_antiquot #[← liftMacroM <| strLitToPattern s, mkAtom "%", mkAtom "$", id]⟩
    | `(stx| &$s:str)        => pure ⟨mkNode `token_antiquot #[← liftMacroM <| strLitToPattern s, mkAtom "%", mkAtom "$", id]⟩
    | `(stx| optional($stx)) => mkSplicePat `optional stx id "?"
    | `(stx| many($stx))     => mkSplicePat `many stx id "*"
    | `(stx| many1($stx))    => mkSplicePat `many stx id "*"
    | `(stx| sepBy($stx, $sep:str $[, $stxsep]? $[, allowTrailingSep]?)) =>
      mkSplicePat `sepBy stx id ((isStrLit? sep).get! ++ "*")
    | `(stx| sepBy1($stx, $sep:str $[, $stxsep]? $[, allowTrailingSep]?)) =>
      mkSplicePat `sepBy stx id ((isStrLit? sep).get! ++ "*")
    -- NOTE: all `interpolatedStr(·)` reuse the same node kind
    | `(stx| interpolatedStr(term)) => pure ⟨Syntax.mkAntiquotNode interpolatedStrKind id⟩
    -- bind through withPosition
    | `(stx| withPosition($stx)) =>
      return (← mkSyntaxAndPat id? id stx)
    | _ => match id? with
      -- if there is a binding, we assume the user knows what they are doing
      | some id => mkAntiquotNode stx id
      -- otherwise `group` the syntax to enforce arity 1, e.g. for `noWs`
      | none    => return (← `(stx| group($stx)), (← mkAntiquotNode stx id))
    pure (stx, pat)
  mkSplicePat kind stx id suffix : CommandElabM Term :=
    return ⟨mkNullNode #[mkAntiquotSuffixSpliceNode kind (← mkAntiquotNode stx id) suffix]⟩
  mkAntiquotNode : TSyntax `stx → Term → CommandElabM Term
    | `(stx| ($stx)), term => mkAntiquotNode stx term
    | `(stx| $id:ident$[:$p:prec]?), term => do
      let kind ← match (← Elab.Term.resolveParserName id) with
        | [(`Lean.Parser.ident, _)] => pure identKind
        | [(`Lean.Parser.Term.ident, _)] => pure identKind
        | [(`Lean.Parser.strLit, _)] => pure strLitKind
        -- a syntax abbrev, assume kind == decl name
        | [(c, _)]      => pure c
        | cs@(_ :: _ :: _) => throwError "ambiguous parser declaration {cs.map (·.1)}"
        | [] =>
          let id := id.getId.eraseMacroScopes
          if Parser.isParserCategory (← getEnv) id then
            return ⟨Syntax.mkAntiquotNode id term (isPseudoKind := true)⟩
          else if (← Parser.isParserAlias id) then
            pure <| (← Parser.getSyntaxKindOfParserAlias? id).getD Name.anonymous
          else
            throwError "unknown parser declaration/category/alias '{id}'"
      pure ⟨Syntax.mkAntiquotNode kind term⟩
    | stx, term =>
      pure ⟨Syntax.mkAntiquotNode Name.anonymous term (isPseudoKind := true)⟩

end Lean.Elab.Command
