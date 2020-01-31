import Init.Lean
open Lean
open Lean.Elab

def run (input : String) (failIff : Bool := true) : MetaIO Unit :=
do env  ← MetaIO.getEnv;
   opts ← MetaIO.getOptions;
   (env, messages) ← liftM $ process input env opts;
   messages.toList.forM $ fun msg => IO.println msg;
   when (failIff && messages.hasErrors) $ throw (IO.userError "errors have been found");
   when (!failIff && !messages.hasErrors) $ throw (IO.userError "there are no errors");
   pure ()

open Lean.Parser

@[termParser] def tst := parser! "(|" >> termParser >> optional (symbolAux ", " >> termParser) >> "|)"

@[termParser] def boo : ParserDescr :=
ParserDescr.node `boo
  (ParserDescr.andthen
    (ParserDescr.symbol "[|" (some 0))
    (ParserDescr.andthen
      (ParserDescr.parser `term 0)
      (ParserDescr.symbol "|]" (some 0))))

open Lean.Elab.Term

@[termElab tst] def elabTst : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
 | `((| $e |)) => pure e
 | _           => throwUnsupportedSyntax

@[termElab boo] def elabBoo : TermElab :=
fun stx expected? =>
  elabTerm (stx.getArg 1) expected?

#eval run "#check [| @id.{1} Nat |]"
#eval run "#check (| id 1 |)"
-- #eval run "#check (| id 1, id 1 |)" -- it will fail

@[termElab tst] def elabTst2 : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
 | `((| $e1, $e2 |)) => `(($e1, $e2))
 | _                 => throwUnsupportedSyntax

-- Now both work

#eval run "#check (| id 1 |)"
#eval run "#check (| id 1, id 2 |)"

new_frontend

declare_syntax_cat foo

syntax "⟨|" term "|⟩" : foo
syntax term : foo
syntax term ">>>" term : foo

syntax [tst3] "FOO " foo : term

macro_rules
| `(FOO ⟨| $t |⟩) => `($t+1)
| `(FOO $t) => `($t)
| `(FOO $t >>> $r) => `($t * $r)

#check FOO ⟨| id 1 |⟩
#check FOO 1
#check FOO 1 >>> 2
