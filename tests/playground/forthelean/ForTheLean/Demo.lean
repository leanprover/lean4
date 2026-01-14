-- -*- origami-fold-style: triple-braces -*-
import ForTheLean.Prelim

open Lean
open Lean.Elab.Command
open Prelim

-- {{{ [synonym]
syntax variant := "-"? wlexem
syntax [synonym] "[synonym " wlexem ("/" (wlexem <|> variant))+ "]" : command
@[command_elab synonym]
def elabSynonym : CommandElab :=
fun stx => match_syntax stx with
| `([synonym $w:ident/ -$w':ident]) => modifyEnv $ fun env => addSynonym env w.getId (w.getId.appendAfter w'.getId.toString)
| `([synonym $w:ident/$w':ident]) => modifyEnv $ fun env => addSynonym env w.getId w'.getId
| _ => throwUnsupportedSyntax
-- }}}

[synonym number/numbers]

-- {{{
syntax indef := "A" <|> "a" <|> "An" <|> "an"
syntax art := "The" <|> "the" <|> indef

syntax notionPattern := art wlexem+

-- all class nouns are added dynamically
declare_syntax_cat classNoun

syntax "Signature." notionPattern "is" indef (classNoun <|> "notion") "." : command
macro_rules
| `(Signature. The $words:wlexem* is a notion.) =>
  let words := words.map Syntax.getId;
  let parsers := words.map mkSyntaxAtom;
  let desc := mkIdent $ mkNameSimple $ "_".intercalate $ words.toList.map toString;
  `(axiom $desc:ident : Type
    syntax_synonyms [$desc] $parsers:syntax* : classNoun
    @[macro $desc] def expandSig : Macro := fun _ => `($desc))
| `(Signature. The $words:wlexem* is a $n.) =>
  let words := words.map Syntax.getId;
  let parsers := words.map mkSyntaxAtom;
  let desc := mkIdent $ mkNameSimple $ "_".intercalate $ words.toList.map toString;
  `(axiom $desc:ident : $n
    syntax_synonyms [$desc] $parsers:syntax* : classNoun
    @[macro $desc] def expandSig : Macro := fun _ => `($desc))
-- }}}

Signature. A real number is a notion.

-- {{{
-- TODO: should be single character
syntax newVar := ident
syntax standFor := "stand" "for"
syntax standForDenote := standFor <|> "denote"
syntax "Let" (sepBy newVar ",") standForDenote (indef)? classNoun "." : command
macro_rules
| `(Let $vs* denote $indef* $noun.) =>
  `(variables ($(vs.getSepElems.map (fun v => v.getArg 0)):ident* : $noun))
-- }}}

Let x,y stand for real numbers.

-- {{{
syntax var := ident  -- TODO: should be single character
syntax uniPredPattern := var "is" wlexem+ var
syntax predPattern := uniPredPattern
syntax "Signature." predPattern "is" (indef)? "atom" "." : command
macro_rules
| `(Signature. $x:var is $words:wlexem* $y:var is an atom.) =>
  let words := words.toList.map Syntax.getId;
  let desc := mkNameSimple $ "_".intercalate $ words.map toString;
  `(axiom $(mkIdent desc):ident : type_of $(x.getArg 0) → type_of $(y.getArg 0) → Prop)
-- }}}

Signature. x is greater than y is an atom.
Signature. A packing of congruent balls in Euclidean three space is a notion.
Signature. The face centered cubic packing is a packing of congruent balls in Euclidean three space.
Let P denote a packing of congruent balls in Euclidean three space.
-- incomplete from here on
Signature. The density of P is a real number.

Theorem The_Kepler_conjecture. No packing of congruent balls in Euclidean three space has density greater than the density of the face centered cubic packing.
