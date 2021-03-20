/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Lean.Elab.Tactic

inductive Location where
  | wildcard
  | targets (hypotheses : Array Name) (type : Bool)

/-
Recall that
```
syntax locationWildcard := "*"
syntax locationTargets  := (colGt ident)+ ("⊢" <|> "|-")?
syntax location         := withPosition("at " locationWildcard <|> locationHyp)
```
-/
def expandLocation (stx : Syntax) : Location :=
  let arg := stx[1]
  if arg.getKind == ``Parser.Tactic.locationWildcard then
    Location.wildcard
  else
    Location.targets (arg[0].getArgs.map fun stx => stx.getId) (!arg[1].isNone)

def expandOptLocation (stx : Syntax) : Location :=
  if stx.isNone then
    Location.targets #[] true
  else
    expandLocation stx[0]

end Lean.Elab.Tactic
