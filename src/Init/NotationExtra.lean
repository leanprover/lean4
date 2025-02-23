/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Extra notation that depends on Init/Meta
-/
prelude
import Init.Data.ToString.Basic
import Init.Data.Array.Subarray
import Init.Conv
import Init.Meta
import Init.While

namespace Lean

-- Auxiliary parsers and functions for declaring notation with binders

syntax unbracketedExplicitBinders := (ppSpace binderIdent)+ (" : " term)?
syntax bracketedExplicitBinders   := "(" withoutPosition((binderIdent ppSpace)+ ": " term) ")"
syntax explicitBinders            := (ppSpace bracketedExplicitBinders)+ <|> unbracketedExplicitBinders

open TSyntax.Compat in
def expandExplicitBindersAux (combinator : Syntax) (idents : Array Syntax) (type? : Option Syntax) (body : Syntax) : MacroM Syntax :=
  let rec loop (i : Nat) (h : i ≤ idents.size) (acc : Syntax) := do
    match i with
    | 0   => pure acc
    | i + 1 =>
      let ident := idents[i][0]
      let acc ← match ident.isIdent, type? with
        | true,  none      => `($combinator fun $ident => $acc)
        | true,  some type => `($combinator fun $ident : $type => $acc)
        | false, none      => `($combinator fun _ => $acc)
        | false, some type => `($combinator fun _ : $type => $acc)
      loop i (Nat.le_of_succ_le h) acc
  loop idents.size (by simp) body

def expandBrackedBindersAux (combinator : Syntax) (binders : Array Syntax) (body : Syntax) : MacroM Syntax :=
  let rec loop (i : Nat) (h : i ≤ binders.size) (acc : Syntax) := do
    match i with
    | 0   => pure acc
    | i+1 =>
      let idents := binders[i][1].getArgs
      let type   := binders[i][3]
      loop i (Nat.le_of_succ_le h) (← expandExplicitBindersAux combinator idents (some type) acc)
  loop binders.size (by simp) body

def expandExplicitBinders (combinatorDeclName : Name) (explicitBinders : Syntax) (body : Syntax) : MacroM Syntax := do
  let combinator := mkCIdentFrom (← getRef) combinatorDeclName
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
  let combinator := mkCIdentFrom (← getRef) combinatorDeclName
  expandBrackedBindersAux combinator #[bracketedExplicitBinders] body

syntax unifConstraint := term patternIgnore(" =?= " <|> " ≟ ") term
syntax unifConstraintElem := colGe unifConstraint ", "?

syntax (docComment)? attrKind "unif_hint" (ppSpace ident)? (ppSpace bracketedBinder)*
  " where " withPosition(unifConstraintElem*) patternIgnore(atomic("|" noWs "-") <|> "⊢") unifConstraint : command

macro_rules
  | `($[$doc?:docComment]? $kind:attrKind unif_hint $(n)? $bs* where $[$cs₁ ≟ $cs₂]* |- $t₁ ≟ $t₂) => do
    let mut body ← `($t₁ = $t₂)
    for (c₁, c₂) in cs₁.zip cs₂ |>.reverse do
      body ← `($c₁ = $c₂ → $body)
    let hint : Ident ← `(hint)
    `($[$doc?:docComment]? @[$kind unification_hint] def $(n.getD hint) $bs* : Sort _ := $body)
end Lean

open Lean

section
open TSyntax.Compat
macro "∃" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Exists xs b
macro "exists" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Exists xs b
macro "Σ" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``Sigma xs b
macro "Σ'" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``PSigma xs b
macro:35 xs:bracketedExplicitBinders " × " b:term:35  : term => expandBrackedBinders ``Sigma xs b
macro:35 xs:bracketedExplicitBinders " ×' " b:term:35 : term => expandBrackedBinders ``PSigma xs b
end

namespace Lean
-- first step of a `calc` block
syntax calcFirstStep := ppIndent(colGe term (" := " term)?)
-- enforce indentation of calc steps so we know when to stop parsing them
syntax calcStep := ppIndent(colGe term " := " term)
syntax calcSteps := ppLine withPosition(calcFirstStep) withPosition((ppLine linebreak calcStep)*)

/-- Step-wise reasoning over transitive relations.
```
calc
  a = b := pab
  b = c := pbc
  ...
  y = z := pyz
```
proves `a = z` from the given step-wise proofs. `=` can be replaced with any
relation implementing the typeclass `Trans`. Instead of repeating the right-
hand sides, subsequent left-hand sides can be replaced with `_`.
```
calc
  a = b := pab
  _ = c := pbc
  ...
  _ = z := pyz
```
It is also possible to write the *first* relation as `<lhs>\n  _ = <rhs> :=
<proof>`. This is useful for aligning relation symbols, especially on longer:
identifiers:
```
calc abc
  _ = bce := pabce
  _ = cef := pbcef
  ...
  _ = xyz := pwxyz
```

`calc` works as a term, as a tactic or as a `conv` tactic.

See [Theorem Proving in Lean 4][tpil4] for more information.

[tpil4]: https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#calculational-proofs
-/
syntax (name := calc) "calc" calcSteps : term

@[inherit_doc «calc»]
syntax (name := calcTactic) "calc" calcSteps : tactic

@[inherit_doc «calc»]
macro tk:"calc" steps:calcSteps : conv =>
  `(conv| tactic => calc%$tk $steps)
end Lean

@[app_unexpander Unit.unit] def unexpandUnit : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(())

@[app_unexpander List.nil] def unexpandListNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `([])

@[app_unexpander List.cons] def unexpandListCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $tail) =>
    match tail with
    | `([])      => `([$x])
    | `([$xs,*]) => `([$x, $xs,*])
    | `(⋯)       => `([$x, $tail]) -- Unexpands to `[x, y, z, ⋯]` for `⋯ : List α`
    | _          => throw ()
  | _ => throw ()

@[app_unexpander List.toArray] def unexpandListToArray : Lean.PrettyPrinter.Unexpander
  | `($(_) [$xs,*]) => `(#[$xs,*])
  | _               => throw ()

@[app_unexpander Prod.mk] def unexpandProdMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $x ($y, $ys,*)) => `(($x, $y, $ys,*))
  | `($(_) $x $y)          => `(($x, $y))
  | _                      => throw ()

@[app_unexpander ite] def unexpandIte : Lean.PrettyPrinter.Unexpander
  | `($(_) $c $t $e) => `(if $c then $t else $e)
  | _                => throw ()

@[app_unexpander Eq.ndrec] def unexpandEqNDRec : Lean.PrettyPrinter.Unexpander
  | `($(_) $m $h) => `($h ▸ $m)
  | _             => throw ()

@[app_unexpander Eq.rec] def unexpandEqRec : Lean.PrettyPrinter.Unexpander
  | `($(_) $m $h) => `($h ▸ $m)
  | _             => throw ()

@[app_unexpander Exists] def unexpandExists : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃ $xs:binderIdent*, $b) => `(∃ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∃ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∃ ($x:ident : $t), $b)
  | _                                              => throw ()

@[app_unexpander Sigma] def unexpandSigma : Lean.PrettyPrinter.Unexpander
  | `($(_) fun ($x:ident : $t) => $b) => `(($x:ident : $t) × $b)
  | _                                  => throw ()

@[app_unexpander PSigma] def unexpandPSigma : Lean.PrettyPrinter.Unexpander
  | `($(_) fun ($x:ident : $t) => $b) => `(($x:ident : $t) ×' $b)
  | _                                 => throw ()

@[app_unexpander Subtype] def unexpandSubtype : Lean.PrettyPrinter.Unexpander
  | `($(_) fun ($x:ident : $type) => $p)  => `({ $x : $type // $p })
  | `($(_) fun $x:ident => $p)            => `({ $x // $p })
  | _                                     => throw ()

@[app_unexpander TSyntax] def unexpandTSyntax : Lean.PrettyPrinter.Unexpander
  | `($f [$k])  => `($f $k)
  | _           => throw ()

@[app_unexpander TSyntaxArray] def unexpandTSyntaxArray : Lean.PrettyPrinter.Unexpander
  | `($f [$k])  => `($f $k)
  | _           => throw ()

@[app_unexpander Syntax.TSepArray] def unexpandTSepArray : Lean.PrettyPrinter.Unexpander
  | `($f [$k] $sep)  => `($f $k $sep)
  | _                => throw ()

@[app_unexpander GetElem.getElem] def unexpandGetElem : Lean.PrettyPrinter.Unexpander
  | `($_ $array $index $_) => `($array[$index])
  | _ => throw ()

@[app_unexpander getElem!] def unexpandGetElem! : Lean.PrettyPrinter.Unexpander
  | `($_ $array $index) => `($array[$index]!)
  | _ => throw ()

@[app_unexpander getElem?] def unexpandGetElem? : Lean.PrettyPrinter.Unexpander
  | `($_ $array $index) => `($array[$index]?)
  | _ => throw ()

@[app_unexpander Array.empty] def unexpandArrayEmpty : Lean.PrettyPrinter.Unexpander
  | _ => `(#[])

@[app_unexpander Array.mkArray0] def unexpandMkArray0 : Lean.PrettyPrinter.Unexpander
  | _ => `(#[])

@[app_unexpander Array.mkArray1] def unexpandMkArray1 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1) => `(#[$a1])
  | _ => throw ()

@[app_unexpander Array.mkArray2] def unexpandMkArray2 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2) => `(#[$a1, $a2])
  | _ => throw ()

@[app_unexpander Array.mkArray3] def unexpandMkArray3 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3) => `(#[$a1, $a2, $a3])
  | _ => throw ()

@[app_unexpander Array.mkArray4] def unexpandMkArray4 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4) => `(#[$a1, $a2, $a3, $a4])
  | _ => throw ()

@[app_unexpander Array.mkArray5] def unexpandMkArray5 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4 $a5) => `(#[$a1, $a2, $a3, $a4, $a5])
  | _ => throw ()

@[app_unexpander Array.mkArray6] def unexpandMkArray6 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4 $a5 $a6) => `(#[$a1, $a2, $a3, $a4, $a5, $a6])
  | _ => throw ()

@[app_unexpander Array.mkArray7] def unexpandMkArray7 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4 $a5 $a6 $a7) => `(#[$a1, $a2, $a3, $a4, $a5, $a6, $a7])
  | _ => throw ()

@[app_unexpander Array.mkArray8] def unexpandMkArray8 : Lean.PrettyPrinter.Unexpander
  | `($(_) $a1 $a2 $a3 $a4 $a5 $a6 $a7 $a8) => `(#[$a1, $a2, $a3, $a4, $a5, $a6, $a7, $a8])
  | _ => throw ()

/--
Apply function extensionality and introduce new hypotheses.
The tactic `funext` will keep applying the `funext` lemma until the goal target is not reducible to
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
syntax "funext" (ppSpace colGt term:max)* : tactic

macro_rules
  | `(tactic|funext) => `(tactic| repeat (apply funext; intro))
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

/--
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
syntax (name := Lean.Parser.Command.classAbbrev)
  declModifiers "class " "abbrev " declId bracketedBinder* (":" term)?
  ":=" withPosition(group(colGe term ","?)*) : command

macro_rules
  | `($mods:declModifiers class abbrev $id $params* $[: $ty]? := $[ $parents $[,]? ]*) =>
    let ctor := mkIdentFrom id <| id.raw[0].getId.modifyBase (. ++ `mk)
    `($mods:declModifiers class $id $params* $[: $ty:term]? extends $[$parents:term],*
      attribute [instance] $ctor)

macro_rules
  | `(haveI $hy:hygieneInfo $bs* $[: $ty]? := $val; $body) =>
    `(haveI $(HygieneInfo.mkIdent hy `this (canonical := true)) $bs* $[: $ty]? := $val; $body)
  | `(haveI _ $bs* := $val; $body) => `(haveI x $bs* : _ := $val; $body)
  | `(haveI _ $bs* : $ty := $val; $body) => `(haveI x $bs* : $ty := $val; $body)
  | `(haveI $x:ident $bs* := $val; $body) => `(haveI $x $bs* : _ := $val; $body)
  | `(haveI $_:ident $_* : $_ := $_; $_) => Lean.Macro.throwUnsupported -- handled by elab

macro_rules
  | `(letI $hy:hygieneInfo $bs* $[: $ty]? := $val; $body) =>
    `(letI $(HygieneInfo.mkIdent hy `this (canonical := true)) $bs* $[: $ty]? := $val; $body)
  | `(letI _ $bs* := $val; $body) => `(letI x $bs* : _ := $val; $body)
  | `(letI _ $bs* : $ty := $val; $body) => `(letI x $bs* : $ty := $val; $body)
  | `(letI $x:ident $bs* := $val; $body) => `(letI $x $bs* : _ := $val; $body)
  | `(letI $_:ident $_* : $_ := $_; $_) => Lean.Macro.throwUnsupported -- handled by elab


namespace Lean
syntax cdotTk := patternIgnore("· " <|> ". ")
/-- `· tac` focuses on the main goal and tries to solve it using `tac`, or else fails. -/
syntax (name := cdot) cdotTk tacticSeqIndentGt : tactic

/--
  Similar to `first`, but succeeds only if one the given tactics solves the current goal.
-/
syntax (name := solveTactic) "solve" withPosition((ppDedent(ppLine) colGe "| " tacticSeq)+) : tactic

macro_rules
  | `(tactic| solve $[| $ts]* ) => `(tactic| focus first $[| ($ts); done]*)

macro:50 e:term:51 " matches " p:sepBy1(term:51, " | ") : term =>
  `(((match $e:term with | $[$p:term]|* => true | _ => false) : Bool))

end Lean

/-- `{ a, b, c }` syntax, powered by the `Singleton` and `Insert` typeclasses. -/
syntax "{" term,+ "}" : term

macro_rules
  | `({$x:term}) => `(singleton $x)
  | `({$x:term, $xs:term,*}) => `(insert $x {$xs:term,*})

recommended_spelling "singleton" for "{x}" in [singleton, «term{_}»]

namespace Lean

/-- Unexpander for the `{ x }` notation. -/
@[app_unexpander singleton]
def singletonUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => `({ $a:term })
  | _ => throw ()

/-- Unexpander for the `{ x, y, ... }` notation. -/
@[app_unexpander insert]
def insertUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a { $ts:term,* }) => `({$a:term, $ts,*})
  | _ => throw ()

end Lean
