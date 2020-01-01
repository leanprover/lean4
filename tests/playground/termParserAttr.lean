import Init.Lean
open Lean
open Lean.Elab

def run (input : String) (failIff : Bool := true) : MetaIO Unit :=
do env  ← MetaIO.getEnv;
   opts ← MetaIO.getOptions;
   let (env, messages) := process input env opts;
   messages.toList.forM $ fun msg => IO.println msg;
   when (failIff && messages.hasErrors) $ throw (IO.userError "errors have been found");
   when (!failIff && !messages.hasErrors) $ throw (IO.userError "there are no errors");
   pure ()

open Lean.Parser
@[termParser] def tst := parser! "(|" >> termParser >> "|)"

@[termParser] def boo : ParserDescr :=
ParserDescr.node `boo
  (ParserDescr.andthen
    (ParserDescr.symbol "[|" 0)
    (ParserDescr.andthen
      (ParserDescr.parser `term 0)
      (ParserDescr.symbol "|]" 0)))

#eval run "#check [| @id.{1} Nat |]"
#eval run "#check (| id 1 |)"
