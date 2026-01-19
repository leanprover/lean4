import Lean

open Lean Elab Tactic Doc

/-!
This test ensures that tactic user names are kept unambiguous.
-/
#eval show MetaM Unit from do
  let firsts ← firstTacticTokens

  -- Compute a reverse mapping from first tokens to their syntax kinds
  let mut rev : Std.HashMap String (List Name) := {}
  for (k, firstTok) in firsts do
    rev := rev.alter firstTok fun x? => x?.map (k :: ·) |>.getD [k]

  -- Check each for ambiguity
  for (firstTok, kindsForToken) in rev do

    -- Skip kinds that are alternative syntax for some user-facing parser
    let kindsForToken ← kindsForToken.filterM fun k => do
      pure <| (Parser.Tactic.Doc.alternativeOfTactic (← getEnv) k).isNone

    -- If it's ambiguous, log an error.
    if kindsForToken.length > 1 then
      let kinds := MessageData.andList <| kindsForToken.map (m!"`{.ofConstName ·}`")
      logError m!"`{firstTok}` is the ambiguous first token for {kinds}"

/-!
This test ensures that tactic user names are found for all the tactics that we ship.
-/
#eval show MetaM Unit from do
  let firsts ← firstTacticTokens
  let some tactics := (Lean.Parser.parserExtension.getState (← getEnv)).categories.find? `tactic
    | return
  for (t, ()) in tactics.kinds do
    if t == ``Lean.Parser.Tactic.nestedTactic then continue
    unless firsts.contains t do
      logError m!"Couldn't find the first token for tactic syntax kind {t}"
