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

macro "Macro.trace[" id:ident "]" s:interpolatedStr(term) : term =>
  `(Macro.trace $(quote id.getId.eraseMacroScopes) (s! $s))

-- Auxiliary parsers and functions for declaring notation with binders

syntax unbracketedExplicitBinders := binderIdent+ (" : " term)?
syntax bracketedExplicitBinders   := "(" binderIdent+ " : " term ")"
syntax explicitBinders            := bracketedExplicitBinders+ <|> unbracketedExplicitBinders

open TSyntax.Compat in
def expandExplicitBindersAux (combinator : Syntax) (idents : Array Syntax) (type? : Option Syntax) (body : Syntax) : MacroM Syntax :=
  let rec loop (i : Nat) (acc : Syntax) := do
    match i with
    | 0   => pure acc
    | i+1 =>
      let ident := idents[i]![0]
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
      let idents := binders[i]![1].getArgs
      let type   := binders[i]![3]
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

macro_rules
  | `($kind:attrKind unif_hint $(n)? $bs:bracketedBinder* where $[$cs₁:term ≟ $cs₂]* |- $t₁:term ≟ $t₂) => do
    let mut body ← `($t₁ = $t₂)
    for (c₁, c₂) in cs₁.zip cs₂ |>.reverse do
      body ← `($c₁ = $c₂ → $body)
    let hint : Ident ← `(hint)
    `(@[$kind:attrKind unificationHint] def $(n.getD hint):ident $bs:bracketedBinder* : Sort _ := $body)
end Lean

open Lean

macro "∃ " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Exists xs b
macro "exists" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Exists xs b
macro "Σ" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Sigma xs b
macro "Σ'" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``PSigma xs b
macro:35 xs:bracketedExplicitBinders " × " b:term:35  : term => expandBrackedBinders ``Sigma xs b
macro:35 xs:bracketedExplicitBinders " ×' " b:term:35 : term => expandBrackedBinders ``PSigma xs b

-- enforce indentation of calc steps so we know when to stop parsing them
syntax calcStep := ppIndent(colGe term " := " withPosition(term))
syntax (name := calc) "calc" ppLine withPosition((calcStep ppLine)+) : term

macro "calc " steps:withPosition(calcStep+) : tactic => `(exact calc $steps*)

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

@[appUnexpander TSyntax] def unexpandTSyntax : Lean.PrettyPrinter.Unexpander
  | `($f [$k])  => `($f $k)
  | _           => throw ()

@[appUnexpander TSyntaxArray] def unexpandTSyntaxArray : Lean.PrettyPrinter.Unexpander
  | `($f [$k])  => `($f $k)
  | _           => throw ()

@[appUnexpander Syntax.TSepArray] def unexpandTSepArray : Lean.PrettyPrinter.Unexpander
  | `($f [$k] $sep)  => `($f $k $sep)
  | _                => throw ()

@[appUnexpander GetElem.getElem] def unexpandGetElem : Lean.PrettyPrinter.Unexpander
  | `(getElem $array $index $_) => `($array[$index])
  | _ => throw ()

@[appUnexpander getElem!] def unexpandGetElem! : Lean.PrettyPrinter.Unexpander
  | `(getElem! $array $index) => `($array[$index]!)
  | _ => throw ()

@[appUnexpander getElem?] def unexpandGetElem? : Lean.PrettyPrinter.Unexpander
  | `(getElem? $array $index) => `($array[$index]?)
  | _ => throw ()

@[appUnexpander getElem'] def unexpandGetElem' : Lean.PrettyPrinter.Unexpander
  | `(getElem' $array $index $h) => `($array[$index]'$h)
  | _ => throw ()

/--
Apply function extensionality and introduce new hypotheses.
The tactic `funext` will keep applying new the `funext` lemma until the goal target is not reducible to
```
  |-  ((fun x => ...) = (fun x => ...))
```
The variant `funext h₁ ... hₙ` applies `funext` `n` times, and uses the given identifiers to name the new hypotheses.
Patterns can be used like in the `intro` tactic. Example, given a goal
```
  |-  ((fun x : Nat × Bool => ...) = (fun x => ...))
```
`funext (a, b)` applies `funext` once and performs pattern matching on the newly introduced pair.
-/
syntax "funext " (colGt term:max)+ : tactic

macro_rules
  | `(tactic|funext $x) => `(tactic| apply funext; intro $x:term)
  | `(tactic|funext $x $xs*) => `(tactic| apply funext; intro $x:term; funext $xs*)

macro_rules
  | `(%[ $[$x],* | $k ]) =>
    if x.size < 8 then
      x.foldrM (β := Term) (init := k) fun x k =>
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
  | `($mods:declModifiers class abbrev $id $params* $[: $ty]? := $[ $parents $[,]? ]*) =>
    let ctor := mkIdentFrom id <| id.raw[0].getId.modifyBase (. ++ `mk)
    `($mods:declModifiers class $id $params* extends $[$parents:term],* $[: $ty]?
      attribute [instance] $ctor)

/-- `· tac` focuses on the main goal and tries to solve it using `tac`, or else fails. -/
syntax ("·" <|> ".") ppHardSpace many1Indent(tactic ";"? ppLine) : tactic
macro_rules
  | `(tactic| ·%$dot $[$tacs:tactic $[;%$sc]?]*) => `(tactic| {%$dot $[$tacs:tactic $[;%$sc]?]*})

/--
  Similar to `first`, but succeeds only if one the given tactics solves the current goal.
-/
syntax (name := solve) "solve " withPosition((colGe "|" tacticSeq)+) : tactic

macro_rules
  | `(tactic| solve $[| $ts]* ) => `(tactic| focus first $[| ($ts); done]*)

namespace Lean
/- `repeat` and `while` notation -/

inductive Loop where
  | mk

@[inline]
partial def Loop.forIn {β : Type u} {m : Type u → Type v} [Monad m] (_ : Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop b
  loop init

instance : ForIn m Loop Unit where
  forIn := Loop.forIn

syntax "repeat " doSeq : doElem

macro_rules
  | `(doElem| repeat $seq) => `(doElem| for _ in Loop.mk do $seq)

syntax "while " ident " : " termBeforeDo " do " doSeq : doElem

macro_rules
  | `(doElem| while $h : $cond do $seq) => `(doElem| repeat if $h : $cond then $seq else break)

syntax "while " termBeforeDo " do " doSeq : doElem

macro_rules
  | `(doElem| while $cond do $seq) => `(doElem| repeat if $cond then $seq else break)

syntax "repeat " doSeq " until " term : doElem

macro_rules
  | `(doElem| repeat $seq until $cond) => `(doElem| repeat do $seq; if $cond then break)

macro:50 e:term:51 " matches " p:sepBy1(term:51, "|") : term =>
  `(((match $e:term with | $[$p:term]|* => true | _ => false) : Bool))

end Lean
