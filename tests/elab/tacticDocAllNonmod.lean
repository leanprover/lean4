import Lean.Elab.Tactic.Doc

/-!
This test checks that the first tokens are found for the tactics that ship with Lean when not in a
module.

In the past, the first token detection code attempted to process the descriptor in the environment;
this failed in modules because the parser was not loaded. This test, along with tacticDocAllModule,
check that the code works correctly both in and out of modules.
-/

open Lean.Elab.Tactic.Doc

#guard_msgs in
open Lean in
#eval do
  let docs ← allTacticDocs
  let userNames := docs.map TacticDoc.userName
  if userNames.size < 50 then
    throwError "Implausibly few user names found: {userNames}"
  for n in userNames do
    if n.startsWith "Lean.Parser.Tactic" && n ≠ "Lean.Parser.Tactic.nestedTactic" then
      logError "Didn't find a first token for tactic parser {n}"
