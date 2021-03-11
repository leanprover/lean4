/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Lean.Elab.Tactic

inductive Location where
  | wildcard
  | target
  | localDecls (userNames : Array Name)

/-
Recall that
```
def locationWildcard := leading_parser "*"
def locationTarget   := leading_parser unicodeSymbol "⊢" "|-"
def locationHyp      := leading_parser many1 ident
def location         := leading_parser "at " >> (locationWildcard <|> locationTarget <|> locationHyp)
```
-/
def expandLocation (stx : Syntax) : Location :=
  let arg := stx[1]
  if arg.getKind == ``Parser.Tactic.locationWildcard then Location.wildcard
  else if arg.getKind == ``Parser.Tactic.locationTarget then Location.target
  else Location.localDecls $ arg[0].getArgs.map fun stx => stx.getId

def expandOptLocation (stx : Syntax) : Location :=
  if stx.isNone then
    Location.target
  else
    expandLocation stx[0]

end Lean.Elab.Tactic
