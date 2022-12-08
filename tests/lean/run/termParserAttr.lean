import Lean

open Lean
open Lean.Elab

def runCore (input : String) (failIff : Bool := true) : CoreM Unit := do
let env  ← getEnv;
let opts ← getOptions;
let (env, messages) ← process input env opts;
messages.toList.forM fun msg => do IO.println (← msg.toString)
if failIff && messages.hasErrors then throwError "errors have been found";
if !failIff && !messages.hasErrors then throwError "there are no errors";
pure ()

open Lean.Parser

@[term_parser] def tst := leading_parser "(|" >> termParser >> Parser.optional (symbol ", " >> termParser) >> "|)"

def tst2 : Parser := symbol "(||" >> termParser >> symbol "||)"

@[term_parser] def boo : ParserDescr :=
ParserDescr.node `boo 10
  (ParserDescr.binary `andthen
    (ParserDescr.symbol "[|")
    (ParserDescr.binary `andthen
      (ParserDescr.cat `term 0)
      (ParserDescr.symbol "|]")))

@[term_parser] def boo2 : ParserDescr :=
ParserDescr.node `boo2 10 (ParserDescr.parser `tst2)

open Lean.Elab.Term

@[term_elab tst] def elabTst : TermElab :=
adaptExpander $ fun stx => match stx with
 | `((| $e |)) => pure e
 | _           => throwUnsupportedSyntax

@[term_elab boo] def elabBoo : TermElab :=
fun stx expected? =>
  elabTerm (stx.getArg 1) expected?

@[term_elab boo2] def elabBool2 : TermElab :=
adaptExpander $ fun stx => match stx with
 | `((|| $e ||)) => `($e + 1)
 | _             => throwUnsupportedSyntax

#eval runCore "#check [| @id.{1} Nat |]"
#eval runCore "#check (| id 1 |)"
#eval runCore "#check (|| id 1 ||)"


-- #eval run "#check (| id 1, id 1 |)" -- it will fail

@[term_elab tst] def elabTst2 : TermElab :=
adaptExpander $ fun stx => match stx with
 | `((| $e1, $e2 |)) => `(($e1, $e2))
 | _                 => throwUnsupportedSyntax

-- Now both work

#eval runCore "#check (| id 1 |)"
#eval runCore "#check (| id 1, id 2 |)"

declare_syntax_cat foo

syntax "⟨|" term "|⟩" : foo
syntax term : foo
syntax term ">>>" term : foo

syntax (name := tst3) "FOO " foo : term

macro_rules
| `(FOO ⟨| $t |⟩) => `($t+1)
| `(FOO $t:term) => `($t)


#check FOO ⟨| id 1 |⟩
#check FOO 1
#check FOO 1 >>> 2
