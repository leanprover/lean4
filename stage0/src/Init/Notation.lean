/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Prelude

-- DSL for specifying parser precedences and priorities

namespace Lean.Parser.Syntax

syntax:65 [addPrec] prec " + " prec:66 : prec
syntax:65 [subPrec] prec " - " prec:66 : prec

syntax:65 [addPrio] prio " + " prio:66 : prio
syntax:65 [subPrio] prio " - " prio:66 : prio

end Lean.Parser.Syntax

macro "max"  : prec => `(1024)
macro "lead" : prec => `(1023)
macro "(" p:prec ")" : prec => p
/-
  `max:prec` as a term. It is equivalent to `evalPrec! max` for `evalPrec!` defined at `Meta.lean`.
  We use `maxPrec!` to workaround bootstrapping issues. -/
macro "maxPrec!" : term => `(1024)

macro "default" : prio => `(1000)
macro "low"     : prio => `(100)
macro "high"    : prio => `(10000)
macro "(" p:prio ")" : prio => p

-- Basic notation for defining parsers
syntax   stx "+" : stx
syntax   stx "*" : stx
syntax   stx "?" : stx
syntax:2 stx " <|> " stx:1 : stx

macro_rules
  | `(stx| $p +) => `(stx| many1($p))
  | `(stx| $p *) => `(stx| many($p))
  | `(stx| $p ?) => `(stx| optional($p))
  | `(stx| $p₁ <|> $p₂) => `(stx| orelse($p₁, $p₂))

/- Comma-separated sequence. -/
macro:max x:stx ",*"   : stx => `(stx| sepBy($x, ",", ", "))
macro:max x:stx ",+"   : stx => `(stx| sepBy1($x, ",", ", "))
/- Comma-separated sequence with optional trailing comma. -/
macro:max x:stx ",*,?" : stx => `(stx| sepBy($x, ",", ", ", allowTrailingSep))
macro:max x:stx ",+,?" : stx => `(stx| sepBy1($x, ",", ", ", allowTrailingSep))

macro "!" x:stx : stx => `(stx| notFollowedBy($x))

syntax[rawNatLit] "natLit! " num : term

infixr:90 " ∘ "  => Function.comp
infixr:35 " × "  => Prod

infixl:65 " + "  => HAdd.hAdd
infixl:65 " - "  => HSub.hSub
infixl:70 " * "  => HMul.hMul
infixl:70 " / "  => HDiv.hDiv
infixl:70 " % "  => HMod.hMod
infixr:80 " ^ "  => HPow.hPow
prefix:100 "-"   => Neg.neg

-- declare ASCII alternatives first so that the latter Unicode unexpander wins
infix:50 " <= " => HasLessEq.LessEq
infix:50 " ≤ "  => HasLessEq.LessEq
infix:50 " < "  => HasLess.Less
infix:50 " >= " => GreaterEq
infix:50 " ≥ "  => GreaterEq
infix:50 " > "  => Greater
infix:50 " = "  => Eq
infix:50 " == " => BEq.beq
infix:50 " ~= " => HEq
infix:50 " ≅ "  => HEq

infixr:35 " /\\ " => And
infixr:35 " ∧ "   => And
infixr:30 " \\/ " => Or
infixr:30 " ∨   " => Or
notation:max "¬" p:40 => Not p

infixl:35 " && " => and
infixl:30 " || " => or
notation:max "!" b:40 => not b

infixl:65 " ++ " => HAppend.hAppend
infixr:67 " :: " => List.cons

infixr:2   " <|> " => HOrElse.hOrElse
infixr:60  " >> "  => HAndThen.hAndThen
infixl:55  " >>= " => Bind.bind
infixl:60  " <*> " => Seq.seq
infixl:60  " <* "  => SeqLeft.seqLeft
infixr:60  " *> "  => SeqRight.seqRight
infixr:100 " <$> " => Functor.map

macro "if" h:ident " : " c:term " then " t:term " else " e:term : term =>
  `(dite $c (fun $h => $t) (fun $h => $e))

macro "if" c:term " then " t:term " else " e:term : term =>
  `(ite $c $t $e)

macro "if " "let " pat:term " := " d:term " then " t:term " else " e:term : term =>
  `(match $d:term with | $pat:term => $t | _ => $e)

syntax:0 term "<|" term:0 : term

macro_rules
  | `($f $args* <| $a) => let args := args.push a; `($f $args*)
  | `($f <| $a) => `($f $a)

syntax:0 term "|>" term:1 : term

macro_rules
  | `($a |> $f $args*) => let args := args.push a; `($f $args*)
  | `($a |> $f)        => `($f $a)

-- Haskell-like pipe <|
-- Note that we have a whitespace after `$` to avoid an ambiguity with the antiquotations.
syntax:0 term atomic("$" ws) term:0 : term

macro_rules
  | `($f $args* $ $a) => let args := args.push a; `($f $args*)
  | `($f $ $a) => `($f $a)

syntax "{ " ident (" : " term)? " // " term " }" : term

macro_rules
  | `({ $x : $type // $p }) => `(Subtype (fun ($x:ident : $type) => $p))
  | `({ $x // $p })         => `(Subtype (fun ($x:ident : _) => $p))

/-
  `withoutExpected! t` instructs Lean to elaborate `t` without an expected type.
  Recall that terms such as `match ... with ...` and `⟨...⟩` will postpone elaboration until
  expected type is known. So, `withoutExpected!` is not effective in this case. -/
macro "withoutExpectedType! " x:term : term => `(let aux := $x; aux)

syntax "[" term,* "]"  : term
syntax "%[" term,* "|" term "]" : term -- auxiliary notation for creating big list literals

namespace Lean

macro_rules
  | `([ $elems,* ]) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Syntax) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← `(List.cons $(elems.elemsAndSeps[i]) $result))
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← `(List.nil))
    else
      `(%[ $elems,* | List.nil ])

namespace Parser.Tactic

syntax[intro] "intro " notFollowedBy("|") (colGt term:max)* : tactic
syntax[intros] "intros " (colGt (ident <|> "_"))* : tactic
syntax[revert] "revert " (colGt ident)+ : tactic
syntax[clear] "clear " (colGt ident)+ : tactic
syntax[subst] "subst " (colGt ident)+ : tactic
syntax[assumption] "assumption" : tactic
syntax[apply] "apply " term : tactic
syntax[exact] "exact " term : tactic
syntax[refine] "refine " term : tactic
syntax[refine!] "refine! " term : tactic
syntax[case] "case " ident " => " tacticSeq : tactic
syntax[allGoals] "allGoals " tacticSeq : tactic
syntax[focus] "focus " tacticSeq : tactic
syntax[skip] "skip" : tactic
syntax[done] "done" : tactic
syntax[traceState] "traceState" : tactic
syntax[failIfSuccess] "failIfSuccess " tacticSeq : tactic
syntax[generalize] "generalize " atomic(ident " : ")? term:51 " = " ident : tactic
syntax[paren] "(" tacticSeq ")" : tactic
syntax[withReducible] "withReducible " tacticSeq : tactic
syntax[withReducibleAndInstances] "withReducibleAndInstances " tacticSeq : tactic
syntax:2[orelse] tactic "<|>" tactic:1 : tactic
macro "try " t:tacticSeq : tactic => `(($t) <|> skip)


macro "rfl" : tactic => `(exact rfl)
macro "decide!" : tactic => `(exact decide!)
macro "admit" : tactic => `(exact sorry)

syntax locationWildcard := "*"
syntax locationTarget   := "⊢" <|> "|-"
syntax locationHyp      := (colGt ident)+
syntax location         := withPosition("at " locationWildcard <|> locationTarget <|> locationHyp)

syntax[change] "change " term (location)? : tactic
syntax[changeWith] "change " term " with " term (location)? : tactic

syntax rwRule    := ("←" <|> "<-")? term
syntax rwRuleSeq := "[" rwRule,+,? "]"

syntax[rewrite] "rewrite " rwRule (location)? : tactic
syntax[rewriteSeq, high] "rewrite " rwRuleSeq (location)? : tactic
syntax[erewrite] "erewrite " rwRule (location)? : tactic
syntax[erewriteSeq, high] "erewrite " rwRuleSeq (location)? : tactic

syntax[rw] "rw " rwRule (location)? : tactic
syntax[rwSeq, high] "rw " rwRuleSeq (location)? : tactic
syntax[erw] "erw " rwRule (location)? : tactic
syntax[erwSeq, high] "erw " rwRuleSeq (location)? : tactic

private def withCheapRefl (tac : Syntax) : MacroM Syntax :=
  `(tactic| $tac; try (withReducible rfl))

@[macro rw]
def expandRw : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.rewrite |>.setArg 0 (mkAtomFrom stx "rewrite"))

@[macro rwSeq]
def expandRwSeq : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.rewriteSeq |>.setArg 0 (mkAtomFrom stx "rewrite"))

@[macro erw]
def expandERw : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.erewrite |>.setArg 0 (mkAtomFrom stx "erewrite"))

@[macro erwSeq]
def expandERwSeq : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.erewriteSeq |>.setArg 0 (mkAtomFrom stx "erewrite"))

syntax[injection] "injection " term (" with " (colGt (ident <|> "_"))+)? : tactic

syntax[«have»] "have " haveDecl : tactic
syntax[«suffices»] "suffices " sufficesDecl : tactic
syntax[«show»] "show " term : tactic
syntax[«let»] "let " letDecl : tactic
syntax[«let!»] "let! " letDecl : tactic
syntax[letrec] withPosition(atomic(group("let " &"rec ")) letRecDecls) : tactic

syntax inductionAlt  := "| " (ident <|> "_") (ident <|> "_")* " => " (hole <|> syntheticHole <|> tacticSeq)
syntax inductionAlts := "with " withPosition( (colGe inductionAlt)+)
syntax[induction] "induction " term,+ (" using " ident)?  ("generalizing " ident+)? (inductionAlts)? : tactic
syntax casesTarget := atomic(ident " : ")? term
syntax[cases] "cases " casesTarget,+ (" using " ident)? (inductionAlts)? : tactic

syntax matchAlt  := "| " term,+ " => " (hole <|> syntheticHole <|> tacticSeq)
syntax matchAlts := withPosition((colGe matchAlt)+)
syntax[«match»] "match " matchDiscr,+ (" : " term)? " with " matchAlts : tactic

syntax[introMatch] "intro " matchAlts : tactic

syntax[existsIntro] "exists " term : tactic

/- We use a priority > default, to avoid ambiguity with the builtin `have` notation -/
macro[high] "have" x:ident " := " p:term : tactic => `(have $x:ident : _ := $p)

syntax "repeat " tacticSeq : tactic
macro_rules
  | `(tactic| repeat $seq) => `(tactic| (($seq); repeat $seq) <|> skip)

end Parser.Tactic
end Lean
