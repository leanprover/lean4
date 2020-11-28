/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Extra notation that depends on Init/Meta
-/
prelude
import Init.Meta
import Init.Data.Array.Subarray

namespace Lean
-- Auxiliary parsers and functions for declaring notation with binders

syntax binderIdent                := ident <|> "_"
syntax unbracktedExplicitBinders  := binderIdent+ (" : " term)?
syntax bracketedExplicitBinders   := "(" binderIdent+ " : " term ")"
syntax explicitBinders            := bracketedExplicitBinders+ <|> unbracktedExplicitBinders

def expandExplicitBindersAux (combinator : Syntax) (idents : Array Syntax) (type? : Option Syntax) (body : Syntax) : MacroM Syntax :=
  let rec loop (i : Nat) (acc : Syntax) := do
    match i with
    | 0   => pure acc
    | i+1 =>
      let ident := idents[i][0]
      let acc ← match ident.isIdent, type? with
        | true,  none      => `($combinator fun $ident => $acc)
        | true,  some type => `($combinator fun $ident:ident : $type => $acc)
        | false, none      => `($combinator fun _ => $acc)
        | false, some type => `($combinator fun _ : $type => $acc)
      loop i (acc.copyInfo (← getRef))
  loop idents.size body

def expandBrackedBindersAux (combinator : Syntax) (binders : Array Syntax) (body : Syntax) : MacroM Syntax :=
  let rec loop (i : Nat) (acc : Syntax) := do
    match i with
    | 0   => pure acc
    | i+1 =>
      let idents := binders[i][1].getArgs
      let type   := binders[i][3]
      loop i (← expandExplicitBindersAux combinator idents (some type) acc)
  loop binders.size body

def expandExplicitBinders (combinatorDeclName : Name) (explicitBinders : Syntax) (body : Syntax) : MacroM Syntax := do
  let combinator := mkIdentFrom (← getRef) combinatorDeclName
  let explicitBinders := explicitBinders[0]
  if explicitBinders.getKind == `Lean.unbracktedExplicitBinders then
    let idents   := explicitBinders[0].getArgs
    let type? := if explicitBinders[1].isNone then none else some explicitBinders[1][1]
    expandExplicitBindersAux combinator idents type? body
  else if explicitBinders.getArgs.all (·.getKind == `Lean.bracketedExplicitBinders) then
    expandBrackedBindersAux combinator explicitBinders.getArgs body
  else
    Macro.throwError "unexpected explicit binder"

def expandBrackedBinders (combinatorDeclName : Name) (bracketedExplicitBinders : Syntax) (body : Syntax) : MacroM Syntax := do
  let combinator := mkIdentFrom (← getRef) combinatorDeclName
  expandBrackedBindersAux combinator #[bracketedExplicitBinders] body

structure UnificationConstraint.{u} where
  {α : Type u}
  lhs : α
  rhs : α

structure UnificationHint.{u} where
  constraints : List UnificationConstraint.{u}
  pattern     : UnificationConstraint.{u}

syntax unifConstraint := term:50 (" =?= " <|> " ≟ ") term:50
syntax unifConstraintElem := colGe unifConstraint ", "?

syntax "unif_hint " bracketedBinder* " where " withPosition(unifConstraintElem*) ("|-" <|> "⊢ ") unifConstraint : command

macro_rules
  | `(unif_hint $bs* where $cs* |- $p) => do
    let mut csNew ← `([])
    for c in cs.reverse do
      csNew ← `((UnificationConstraint.mk $(c[0][0]) $(c[0][2])) :: $csNew)
    `(@[unificationHint] def hint $bs:explicitBinder* : UnificationHint := {
        constraints := $csNew
        pattern := UnificationConstraint.mk $(p[0]) $(p[2])
      })

end Lean

open Lean

macro "∃" xs:explicitBinders ", " b:term : term => expandExplicitBinders `Exists xs b
macro "exists" xs:explicitBinders ", " b:term : term => expandExplicitBinders `Exists xs b
macro "Σ" xs:explicitBinders ", " b:term : term => expandExplicitBinders `Sigma xs b
macro "Σ'" xs:explicitBinders ", " b:term : term => expandExplicitBinders `PSigma xs b
macro:25 xs:bracketedExplicitBinders "×" b:term : term => expandBrackedBinders `Sigma xs b
macro:25 xs:bracketedExplicitBinders "×'" b:term : term => expandBrackedBinders `PSigma xs b

syntax "funext " (colGt term:max)+ : tactic

macro_rules
  | `(tactic|funext $xs*) =>
    if xs.size == 1 then
      `(tactic| apply funext; intro $(xs[0]):term)
    else
      `(tactic| apply funext; intro $(xs[0]):term; funext $(xs[1:])*)
