/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term

namespace Lean.Elab.Term
/-
  Recall that
  ```
  def typeSpec := leading_parser " : " >> termParser
  def optType : Parser := optional typeSpec
  ```
-/
def expandOptType (ref : Syntax) (optType : Syntax) : Syntax :=
  if optType.isNone then
    mkHole ref
  else
    optType[0][1]

open Lean.Parser.Term

/- Helper function for `expandEqnsIntoMatch` -/
def getMatchAltsNumPatterns (matchAlts : Syntax) : Nat :=
  let alt0 := matchAlts[0][0]
  let pats := alt0[1][0].getSepArgs
  pats.size

/--
  Expand a match alternative such as `| 0 | 1 => rhs` to an array containing `| 0 => rhs` and `| 1 => rhs`.
-/
def expandMatchAlt (matchAlt : Syntax) : Array Syntax :=
  let patss := matchAlt[1]
  let rhs   := matchAlt[3]
  if patss.getArgs.size ≤ 1 then
    #[matchAlt]
  else
    patss.getSepArgs.map fun pats =>
      let patss := mkNullNode #[pats]
      matchAlt.setArg 1 patss

def shouldExpandMatchAlt (matchAlt : Syntax) : Bool :=
  let patss := matchAlt[1]
  patss.getArgs.size > 1

def expandMatchAlts? (stx : Syntax) : MacroM (Option Syntax) := do
  match stx with
  | `(match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*) =>
    if alts.any shouldExpandMatchAlt then
      let alts := alts.foldl (init := #[]) fun alts alt => alts ++ expandMatchAlt alt
      `(match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*)
    else
      return none
  | _ => return none

end Lean.Elab.Term
