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
def expandMacroArg (stx : Syntax) : MacroM (Syntax × Syntax) := do
  let (id?, id, stx) ← match (← expandMacros stx) with
    | `(macroArg| $id:ident:$stx) => pure (some id, id, stx)
    | `(macroArg| $stx:stx)       => pure (none, (← `(x)), stx)
    | _                           => Macro.throwUnsupported
  let pat ← match stx with
    | `(stx| $s:str)      => pure <| mkNode `token_antiquot #[← strLitToPattern s, mkAtom "%", mkAtom "$", id]
    | `(stx| &$s:str)     => pure <| mkNode `token_antiquot #[← strLitToPattern s, mkAtom "%", mkAtom "$", id]
    | `(stx| optional($stx)) => pure <| mkSplicePat `optional id "?"
    | `(stx| many($stx))     => pure <| mkSplicePat `many id "*"
    | `(stx| many1($stx))    => pure <| mkSplicePat `many id "*"
    | `(stx| sepBy($stx, $sep:str $[, $stxsep]? $[, allowTrailingSep]?)) =>
      pure <| mkSplicePat `sepBy id ((isStrLit? sep).get! ++ "*")
    | `(stx| sepBy1($stx, $sep:str $[, $stxsep]? $[, allowTrailingSep]?)) =>
      pure <| mkSplicePat `sepBy id ((isStrLit? sep).get! ++ "*")
    | _ => match id? with
      -- if there is a binding, we assume the user knows what they are doing
      | some id => pure <| mkAntiquotNode id
      -- otherwise `group` the syntax to enforce arity 1, e.g. for `noWs`
      | none    => return (← `(stx| group($stx)), mkAntiquotNode id)
  pure (stx, pat)
where mkSplicePat kind id suffix :=
  mkNullNode #[mkAntiquotSuffixSpliceNode kind (mkAntiquotNode id) suffix]

end Lean.Elab.Command
