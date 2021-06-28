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

/- Convert `macro` argument into a `syntax` command item -/
def expandMacroArgIntoSyntaxItem : Macro
  | `(macroArg|$id:ident:$stx)    => stx
  -- can't match against `$s:strLit%$id` because the latter part would be interpreted as an antiquotation on the token
  -- `strLit`.
  | `(macroArg|$s:macroArgSymbol) => `(stx|$(s[0]):strLit)
  | _                             => Macro.throwUnsupported

/- Convert `macro` arg into a pattern element -/
def expandMacroArgIntoPattern (stx : Syntax) : MacroM Syntax := do
  match (← expandMacros stx) with
  | `(macroArg|$id:ident:optional($stx)) =>
    mkSplicePat `optional id "?"
  | `(macroArg|$id:ident:many($stx)) =>
    mkSplicePat `many id "*"
  | `(macroArg|$id:ident:many1($stx)) =>
    mkSplicePat `many id "*"
  | `(macroArg|$id:ident:sepBy($stx, $sep:strLit $[, $stxsep]? $[, allowTrailingSep]?)) =>
    mkSplicePat `sepBy id ((isStrLit? sep).get! ++ "*")
  | `(macroArg|$id:ident:sepBy1($stx, $sep:strLit $[, $stxsep]? $[, allowTrailingSep]?)) =>
    mkSplicePat `sepBy id ((isStrLit? sep).get! ++ "*")
  | `(macroArg|$id:ident:$stx) => mkAntiquotNode id
  | `(macroArg|$s:strLit) => strLitToPattern s
  -- `"tk"%id` ~> `"tk"%$id`
  | `(macroArg|$s:macroArgSymbol) => mkNode `token_antiquot #[← strLitToPattern s[0], mkAtom "%", mkAtom "$", s[1][1]]
  | _                          => Macro.throwUnsupported
  where mkSplicePat kind id suffix :=
    mkNullNode #[mkAntiquotSuffixSpliceNode kind (mkAntiquotNode id) suffix]

end Lean.Elab.Command
