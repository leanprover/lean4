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
      loop i acc
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

syntax unifConstraint := term (" =?= " <|> " ≟ ") term
syntax unifConstraintElem := colGe unifConstraint ", "?

syntax attrKind "unif_hint " (ident)? bracketedBinder* " where " withPosition(unifConstraintElem*) ("|-" <|> "⊢ ") unifConstraint : command

private def mkHintBody (cs : Array Syntax) (p : Syntax) : MacroM Syntax := do
  let mut body ← `($(p[0]) = $(p[2]))
  for c in cs.reverse do
    body ← `($(c[0][0]) = $(c[0][2]) → $body)
  return body

macro_rules
  | `($kind:attrKind unif_hint $bs:explicitBinder* where $cs* |- $p) => do
    let body ← mkHintBody cs p
    `(@[$kind:attrKind unificationHint] def hint $bs:explicitBinder* : Sort _ := $body)
  | `($kind:attrKind unif_hint $n:ident $bs* where $cs* |- $p) => do
    let body ← mkHintBody cs p
    `(@[$kind:attrKind unificationHint] def $n:ident $bs:explicitBinder* : Sort _ := $body)
end Lean

open Lean

macro "∃" xs:explicitBinders ", " b:term : term => expandExplicitBinders `Exists xs b
macro "exists" xs:explicitBinders ", " b:term : term => expandExplicitBinders `Exists xs b
macro "Σ" xs:explicitBinders ", " b:term : term => expandExplicitBinders `Sigma xs b
macro "Σ'" xs:explicitBinders ", " b:term : term => expandExplicitBinders `PSigma xs b
macro:35 xs:bracketedExplicitBinders "×" b:term:35  : term => expandBrackedBinders `Sigma xs b
macro:35 xs:bracketedExplicitBinders "×'" b:term:35 : term => expandBrackedBinders `PSigma xs b

syntax "funext " (colGt term:max)+ : tactic

macro_rules
  | `(tactic|funext $xs*) =>
    if xs.size == 1 then
      `(tactic| apply funext; intro $(xs[0]):term)
    else
      `(tactic| apply funext; intro $(xs[0]):term; funext $(xs[1:])*)

macro_rules
  | `(%[ $[$x],* | $k ]) =>
    if x.size < 8 then
      x.foldrM (init := k) fun x k =>
        `(List.cons $x $k)
    else
      let m := x.size / 2
      let y := x[m:]
      let z := x[:m]
      `(let y := %[ $[$y],* | $k ]
        %[ $[$z],* | y ])

/-
  Expands
  ```
  class abbrev C <params> := D_1, ..., D_n
  ```
  into
  ```
  class C <params> extends D_1, ..., D_n
  instance <params> [D_1] ... [D_n] : C <params> :=
    C.mk _ ... _ inferInstance ... inferInstance
  ```
-/
syntax "class " "abbrev " ident bracketedBinder* ":=" withPosition(group(colGe term ","?)*) : command

macro_rules
  | `(class abbrev $name:ident $params* := $[ $parents:term $[,]? ]*) => do
    let mut auxBinders := #[]
    let mut typeArgs   := #[]
    let mut ctorArgs   := #[]
    let hole ← `(_)
    for param in params do
      match param with
      | `(bracketedBinder| ( $ids:ident* $[: $type:term]? ) ) =>
         auxBinders := auxBinders.push (← `(bracketedBinder| { $ids:ident* }) )
         typeArgs   := typeArgs ++ ids
         ctorArgs   := ctorArgs ++ ids.map fun _ => hole
      | `(bracketedBinder| [ $id:ident : $type:term ] ) =>
         auxBinders := auxBinders.push param
         typeArgs   := typeArgs.push hole
         ctorArgs   := ctorArgs.push hole
      | `(bracketedBinder| [ $type:term ] ) =>
         auxBinders := auxBinders.push param
         typeArgs   := typeArgs.push hole
         ctorArgs   := ctorArgs.push hole
      | `(bracketedBinder| { $ids:ident* $[: $type ]? } ) =>
         auxBinders := auxBinders.push param
         typeArgs   := typeArgs ++ ids.map fun _ => hole
         ctorArgs   := typeArgs ++ ids.map fun _ => hole
      | _ => Lean.Macro.throwErrorAt param "unexpected binder at `class abbrev` macro"
    let inferInst ← `(inferInstance)
    for parent in parents do
      auxBinders := auxBinders.push (← `(bracketedBinder| [ $parent:term ]))
      ctorArgs   := ctorArgs.push inferInst
    let view := Lean.extractMacroScopes name.getId
    let ctor := mkIdentFrom name { view with name := view.name ++ `mk }.review
    `(class $name:ident $params* extends $[$parents:term],*
      instance $auxBinders:explicitBinder* : @ $name:ident $typeArgs* :=
        @ $ctor:ident $ctorArgs*)

/-
  Similar to `first`, but succeeds only if one the given tactics solves the curretn goal.
-/
syntax "solve " "|"? sepBy1(tacticSeq, "|") : tactic

macro_rules
  | `(tactic| solve $[|]? $ts:tacticSeq|*) => `(tactic| focus first $[($ts); done]|*)
