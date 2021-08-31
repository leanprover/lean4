/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Extra notation that depends on Init/Meta
-/
prelude
import Init.Meta
import Init.Data.Array.Subarray
import Init.Data.ToString
namespace Lean

syntax "Macro.trace[" ident "]" interpolatedStr(term) : term

macro_rules
  | `(Macro.trace[$id] $s) => `(Macro.trace $(quote id.getId) (s! $s))


-- Auxiliary parsers and functions for declaring notation with binders

syntax binderIdent                := ident <|> "_"
syntax unbracketedExplicitBinders := binderIdent+ (" : " term)?
syntax bracketedExplicitBinders   := "(" binderIdent+ " : " term ")"
syntax explicitBinders            := bracketedExplicitBinders+ <|> unbracketedExplicitBinders

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
  if explicitBinders.getKind == ``Lean.unbracketedExplicitBinders then
    let idents   := explicitBinders[0].getArgs
    let type? := if explicitBinders[1].isNone then none else some explicitBinders[1][1]
    expandExplicitBindersAux combinator idents type? body
  else if explicitBinders.getArgs.all (·.getKind == ``Lean.bracketedExplicitBinders) then
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

macro "∃ " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Exists xs b
macro "exists" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Exists xs b
macro "Σ" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Sigma xs b
macro "Σ'" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``PSigma xs b
macro:35 xs:bracketedExplicitBinders " × " b:term:35  : term => expandBrackedBinders ``Sigma xs b
macro:35 xs:bracketedExplicitBinders " ×' " b:term:35 : term => expandBrackedBinders ``PSigma xs b

-- enforce indentation of calc steps so we know when to stop parsing them
syntax calcStep := colGe term " := " withPosition(term)
syntax (name := calc) "calc " withPosition(calcStep+) : term

macro "calc " steps:withPosition(calcStep+) : tactic => `(exact calc $(steps.getArgs)*)

@[appUnexpander Unit.unit] def unexpandUnit : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(())
  | _       => throw ()

@[appUnexpander List.nil] def unexpandListNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `([])
  | _       => throw ()

@[appUnexpander List.cons] def unexpandListCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x [])      => `([$x])
  | `($(_) $x [$xs,*]) => `([$x, $xs,*])
  | _                  => throw ()

@[appUnexpander List.toArray] def unexpandListToArray : Lean.PrettyPrinter.Unexpander
  | `($(_) [$xs,*]) => `(#[$xs,*])
  | _               => throw ()

@[appUnexpander Prod.mk] def unexpandProdMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $x ($y, $ys,*)) => `(($x, $y, $ys,*))
  | `($(_) $x $y)          => `(($x, $y))
  | _                      => throw ()

@[appUnexpander ite] def unexpandIte : Lean.PrettyPrinter.Unexpander
  | `($(_) $c $t $e) => `(if $c then $t else $e)
  | _                => throw ()

@[appUnexpander sorryAx] def unexpandSorryAx : Lean.PrettyPrinter.Unexpander
  | `($(_) _)   => `(sorry)
  | `($(_) _ _) => `(sorry)
  | _           => throw ()

@[appUnexpander Eq.ndrec] def unexpandEqNDRec : Lean.PrettyPrinter.Unexpander
  | `($(_) $m $h) => `($h ▸ $m)
  | _             => throw ()

@[appUnexpander Eq.rec] def unexpandEqRec : Lean.PrettyPrinter.Unexpander
  | `($(_) $m $h) => `($h ▸ $m)
  | _             => throw ()

@[appUnexpander Exists] def unexpandExists : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃ $xs:binderIdent*, $b) => `(∃ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∃ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∃ ($x:ident : $t), $b)
  | _                                              => throw ()

@[appUnexpander Sigma] def unexpandSigma : Lean.PrettyPrinter.Unexpander
  | `($(_) fun ($x:ident : $t) => $b) => `(($x:ident : $t) × $b)
  | _                                  => throw ()

@[appUnexpander PSigma] def unexpandPSigma : Lean.PrettyPrinter.Unexpander
  | `($(_) fun ($x:ident : $t) => $b) => `(($x:ident : $t) ×' $b)
  | _                                 => throw ()

@[appUnexpander Subtype] def unexpandSubtype : Lean.PrettyPrinter.Unexpander
  | `($(_) fun ($x:ident : $type) => $p)  => `({ $x : $type // $p })
  | `($(_) fun $x:ident => $p)            => `({ $x // $p })
  | _                                     => throw ()

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
  attribute [instance] C.mk
  ```
-/
syntax declModifiers "class " "abbrev " declId bracketedBinder* (":" term)?
  ":=" withPosition(group(colGe term ","?)*) : command

macro_rules
  | `($mods:declModifiers class abbrev $id $params* $[: $ty:term]? := $[ $parents:term $[,]? ]*) =>
    let name := id[0]
    let ctor := mkIdentFrom name <| name.getId.modifyBase (. ++ `mk)
    `($mods:declModifiers class $id $params* extends $[$parents:term],* $[: $ty]?
      attribute [instance] $ctor)

/-
  Similar to `first`, but succeeds only if one the given tactics solves the current goal.
-/
syntax (name := solve) "solve " withPosition((group(colGe "|" tacticSeq))+) : tactic

macro_rules
  | `(tactic| solve $[| $ts]* ) => `(tactic| focus first $[| ($ts); done]*)
