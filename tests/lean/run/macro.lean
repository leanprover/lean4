import Init.Lean

open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Command

@[commandParser] def syntax := parser! "syntax" >> many1 (termParser appPrec) >> " : " >> ident

@[commandElab syntax] def elabSyntax : CommandElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(syntax $parts* : $cat) => do
  parts ← parts.mapM (fun part => match_syntax part with
    | `($str:str) => `(Lean.Parser.symbolAux $str)
    | _           => pure part);
  p ← parts.foldlFromM (fun p part => `($p >> $part)) (parts.get! 0) 1;
  -- TODO: trailing parsers
  -- TODO: meaningful, unhygienic def name for selective syntax `open`ing?
  `(@[$cat:ident] def myParser : Lean.Parser.Parser Lean.ParserKind.leading := parser! $p)
| _ => throwUnsupportedSyntax

@[commandParser] def macro := parser! "macro" >> many1Indent Term.matchAlt "'match' alternatives must be indented"

@[commandElab macro] def elabMacro : CommandElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(macro $alts*) => do
  -- TODO: clean up with matchAlt quotation
  k ← match_syntax ((alts.get! 0).getArg 1).getArg 0 with
  | `(`($quot)) => pure quot.getKind
  | stx         => throwUnsupportedSyntax;
  -- TODO: meaningful, unhygienic def name for selective macro `open`ing?
  `(@[termElab $(Lean.mkSimpleIdent k)] def myTermMacro : TermElab := adaptExpander $ fun stx => match_syntax stx with $alts* | _ => throwUnsupportedSyntax @[commandElab $(Lean.mkSimpleIdent k)] def myCommandMacro : Lean.Elab.Command.CommandElab := Lean.Elab.Command.adaptExpander $ fun stx => match_syntax stx with $alts* | _ => Lean.Elab.Command.throwUnsupportedSyntax)
| _ => throwUnsupportedSyntax


abbrev Set (α : Type) := α → Prop
axiom setOf {α : Type} : (α → Prop) → Set α
axiom mem {α : Type} : α → Set α → Prop
axiom univ {α : Type} : Set α
axiom Union {α : Type} : Set (Set α) → Set α

namespace Lean.Parser.Term
@[termParser] def mem := tparser! infixL " ∈ " 100
end Lean.Parser.Term
namespace Lean.Elab.Term
@[termElab mem] def elabMem : TermElab := elabInfixOp `mem
end Lean.Elab.Term


new_frontend
open Lean.Parser

syntax "{" termParser " | " termParser "}" : termParser
macro
| `({$x ∈ $s | $p}) => `(setOf (fun $x => $x ∈ $s ∧ $p))
| `({$x ≤ $e | $p}) => `(setOf (fun $x => $x ≤ $e ∧ $p))
| `({$b      | $r}) => `(setOf (fun $b => $r))

syntax "⋃ " termParser ", " termParser : termParser
macro | `(⋃ $b, $r) => `(Union {$b | $r})

#check ⋃ x,              x = x
#check ⋃ (x : Set Unit), x = x
#check ⋃ x ∈ univ,       x = x


syntax "#check2" termParser : commandParser
macro | `(#check2 $e) => `(#check $e #check $e)

#check2 1
