/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term

namespace Lean.Elab.Term
/--
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

/-- Helper function for `expandEqnsIntoMatch` -/
def getMatchAltsNumPatterns (matchAlts : Syntax) : Nat :=
  let alt0 := matchAlts[0][0]
  let pats := alt0[1][0].getSepArgs
  pats.size

/--
  Expand a match alternative such as `| 0 | 1 => rhs` to an array containing `| 0 => rhs` and `| 1 => rhs`.
-/
def expandMatchAlt (stx : TSyntax ``matchAlt) : MacroM (Array (TSyntax ``matchAlt)) :=
  match stx with
  | `(matchAltExpr| | $[$patss,*]|* => $rhs) =>
     if patss.size ≤ 1 then
       return #[stx]
     else
       patss.mapM fun pats => `(matchAltExpr| | $pats,* => $rhs)
  | _ => return #[stx]

def shouldExpandMatchAlt : TSyntax ``matchAlt → Bool
  | `(matchAltExpr| | $[$patss,*]|* => $_) => patss.size > 1
  | _ => false

def expandMatchAlts? (stx : Syntax) : MacroM (Option Syntax) := do
  match stx with
  | `(match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*) =>
    if alts.any shouldExpandMatchAlt then
      let alts ← alts.foldlM (init := #[]) fun alts alt => return alts ++ (← expandMatchAlt alt)
      `(match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*)
    else
      return none
  | _ => return none

open TSyntax.Compat in
def clearInMatchAlt (stx : TSyntax ``matchAlt) (vars : Array Ident) : TSyntax ``matchAlt :=
  stx.1.modifyArg 3 fun rhs => Unhygienic.run do
    let mut rhs := rhs
    for v in vars do
      rhs ← `(clear% $v; $rhs)
    return rhs

def clearInMatch (stx : Syntax) (vars : Array Ident) : MacroM Syntax := do
  if vars.isEmpty then return stx
  match stx with
  | `(match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*) =>
    let alts := alts.map (clearInMatchAlt · vars)
    `(match $[$gen]? $[$motive]? $discrs,* with $alts:matchAlt*)
  | _ => return stx

end Lean.Elab.Term
