/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Prelude

infixr:90 " ∘ "  => Function.comp
infixr:35 " × "  => Prod

infixl:65 " + "  => Add.add
infixl:65 " - "  => Sub.sub
infixl:70 " * "  => Mul.mul
infixl:70 " / "  => Div.div
infixl:70 " % "  => Mod.mod
infixl:70 " %ₙ " => ModN.modn
infixr:80 " ^ "  => Pow.pow

infix:50 " ≤ "  => HasLessEq.LessEq
infix:50 " <= " => HasLessEq.LessEq
infix:50 " < "  => HasLess.Less
infix:50 " ≥ "  => GreaterEq
infix:50 " >= " => GreaterEq
infix:50 " > "  => Greater
infix:50 " = "  => Eq
infix:50 " == " => BEq.beq
infix:50 " ~= " => HEq
infix:50 " ≅ "  => HEq

infixr:35 " ∧ "   => And
infixr:35 " /\\ " => And
infixr:30 " ∨   " => Or
infixr:30 " \\/ " => Or

infixl:35 " && " => and
infixl:30 " || " => or

infixl:65 " ++ " => Append.append
infixr:67 " :: " => List.cons

infixr:2   " <|> " => OrElse.orElse
infixr:60  " >> "  => AndThen.andThen
infixl:55  " >>= " => Bind.bind
infixl:60  " <*> " => Seq.seq
infixl:60  " <* "  => SeqLeft.seqLeft
infixr:60  " *> "  => SeqRight.seqRight
infixr:100 " <$> " => Functor.map

macro "if" h:ident " : " c:term " then " t:term " else " e:term : term =>
  `(dite $c (fun $h => $t) (fun $h => $e))

macro "if" c:term " then " t:term " else " e:term : term =>
  `(ite $c $t $e)

syntax "[" sepBy(term, ", ") "]"  : term

open Lean in
macro_rules
  | `([ $elems* ]) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Syntax) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← `(List.cons $(elems[i]) $result))
    expandListLit elems.size false (← `(List.nil))

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

macro "!" x:stx : stx => `(stx| notFollowedBy($x))

syntax "{ " ident (" : " term)? " // " term " }" : term

macro_rules
  | `({ $x : $type // $p }) => `(Subtype (fun ($x:ident : $type) => $p))
  | `({ $x // $p })         => `(Subtype (fun ($x:ident : _) => $p))

namespace Lean.Parser.Tactic

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

syntax locationWildcard := "*"
syntax locationTarget   := "⊢" <|> "|-"
syntax locationHyp      := (colGt ident)+
syntax location         := withPosition("at " locationWildcard <|> locationTarget <|> locationHyp)

syntax[change] "change " term (location)? : tactic
syntax[changeWith] "change " term " with " term (location)? : tactic

syntax rwRule    := ("←" <|> "<-")? term
syntax rwRuleSeq := "[" sepBy1T(rwRule, ", ") "]"

syntax[rewrite] (&"rewrite" <|> &"rw") !"[" rwRule (location)? : tactic
syntax[rewriteSeq] (&"rewrite" <|> &"rw") rwRuleSeq (location)? : tactic

syntax:2[orelse] tactic "<|>" tactic:1 : tactic

syntax[injection] "injection " term (" with " (colGt (ident <|> "_"))+)? : tactic

syntax[«have»] "have " haveDecl : tactic
syntax[«suffices»] "suffices " sufficesDecl : tactic
syntax[«show»] "show " term : tactic
syntax[«let»] "let " letDecl : tactic
syntax[«let!»] "let! " letDecl : tactic
syntax[letrec] withPosition(atomic(group("let " &"rec ")) letRecDecls) : tactic

syntax inductionAlt  := (ident <|> "_") (ident <|> "_")* " => " (hole <|> syntheticHole <|> tacticSeq)
syntax inductionAlts := withPosition("| " sepBy1(inductionAlt, colGe "| "))
syntax[induction] "induction " sepBy1(term, ", ") (" using " ident)?  ("generalizing " ident+)? (inductionAlts)? : tactic
syntax casesTarget := atomic(ident " : ")? term
syntax[cases] "cases " sepBy1(casesTarget, ", ") (" using " ident)? (inductionAlts)? : tactic

syntax matchAlt  := sepBy1(term, ", ") " => " (hole <|> syntheticHole <|> tacticSeq)
syntax matchAlts := withPosition("| " sepBy1(matchAlt, colGe "| "))
syntax[«match»] "match " sepBy1(matchDiscr, ", ") (" : " term)? " with " matchAlts : tactic

syntax[introMatch] "intro " matchAlts : tactic

macro "rfl" : tactic => `(exact rfl)
macro "decide!" : tactic => `(exact decide!)
macro "admit" : tactic => `(exact sorry)
/- We use a priority > 0, to avoid ambiguity with the builtin `have` notation -/
macro[1] "have" x:ident ":=" p:term : tactic => `(have $x:ident : _ := $p)

syntax "repeat " tacticSeq : tactic
macro_rules
  | `(tactic| repeat $seq) => `(tactic| (($seq); repeat $seq) <|> skip)

macro "try " t:tacticSeq : tactic => `(($t) <|> skip)

end Lean.Parser.Tactic
