import Lean
namespace Lean.Elab.Command
open Lean
-- to get around missing structure notation support
def modifyEnv (f : Environment → Environment) : CommandElabM Unit :=
modify $ fun s => { s with env := f s.env }
end Lean.Elab.Command

namespace Prelim
open Lean
open Lean.Parser

-- for declaring simple parsers I can still use within other `syntax`
@[command_parser] def syntaxAbbrev := parser! "syntax " >> ident >> " := " >> many1 syntaxParser
@[macro syntaxAbbrev] def elabSyntaxAbbrev : Macro :=
fun stx => match_syntax stx with
| `(syntax $id := $p*) => `(declare_syntax_cat $id  syntax:0 $p* : $id)
| _ => Macro.throwUnsupported

def mkSyntaxAtom (n : Name) : Syntax :=
Syntax.node `Lean.Parser.Syntax.atom #[Lean.mkStxStrLit n.toString, mkNullNode]

-- store known synonyms of a word

-- HACK: can't define new environment extension at runtime, so I'm reusing this matching one...
def addSynonym (env : Environment) (a : Name) (e : Name) : Environment :=
addAlias env (`_subst ++ a) (e)

def getSynonyms (env : Environment) (a : Name) : List Name :=
match (aliasExtension.getState env).find? (`_subst ++ a) with
| none    => []
| some es => es

def checkPrev (p : Syntax → Bool) (errorMsg : String) : Parser :=
{ fn := fun c s =>
  let prev := s.stxStack.back;
  if p prev then s else s.mkError errorMsg }

-- a word lexem is any identifier/keyword except for variables and "is"
def wlexem : Parser :=
try (rawIdent >> checkPrev (fun stx => stx.getId.toString.length > 1 && not ([`is].contains stx.getId)) "")
end Prelim


open Lean
open Lean.Elab
open Lean.Elab.Command
open Prelim

syntax [type_of] "type_of" term:max : term
@[term_elab «type_of»]
def elabTypeOf : Term.TermElab :=
fun stx _ => match_syntax stx with
| `(type_of $e) =>
  Term.elabTerm e none >>= Term.inferType e
| _ => Term.throwUnsupportedSyntax

syntax [syntax_synonyms] "syntax_synonyms" "[" ident "]" «syntax»+ ":" ident : command
@[command_elab «syntax_synonyms»] def elabSyntaxSynonyms : CommandElab :=
fun stx => match_syntax stx with
| `(syntax_synonyms [$kind] $stxs* : $cat) =>
  -- TODO: do notation
  getEnv >>= fun env =>
  -- map word w with synonyms w1... to syntax ("w" <|> "w1" <|> ...)
  let stxs := stxs.map (fun stx =>
    if stx.isOfKind `Lean.Parser.Syntax.atom then
      let word := (Lean.Syntax.isStrLit? (stx.getArg 0)).getD "";
      let substs := getSynonyms env (mkNameSimple word);
      -- TODO: `(syntax|` antiquotation
      -- TODO: `foldl1` would be nice
      substs.foldl (fun stx word => Syntax.node `Lean.Parser.Syntax.orelse #[stx, mkAtom "<|>", mkSyntaxAtom word])
        stx
    else stx);
  `(syntax [$kind] $stxs:syntax* : $cat) >>= elabCommand
| _ => throwUnsupportedSyntax

-- HACK: get `wlexem` into `syntax` world
declare_syntax_cat wlexem
@[wlexemParser] def wlexem := Prelim.wlexem
