import Lean

/-!
# `hygieneInfo` antiquotations keep the preceding token's trailing whitespace

`hygieneInfoFn` moves the previous token's trailing whitespace onto the `hygieneInfo` node it
produces. That edit reaches below its own stack frame, so it is not undone by backtracking. When a
`hygieneInfo` antiquotation matched, `withAntiquot` used to run `hygieneInfoFn` as well and then
throw its result away, and the whitespace went with it.
-/

open Lean

elab "#reprint " s:str : command => Elab.Command.liftTermElabM do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term s.getString
  logInfo s!"‹{stx.reprint.getD "<reprint failed>"}›"

/-!
A `hygieneInfo` antiquotation after `·`. The space after `·` used to disappear.
-/
/-- info: ‹`(· $h:hygieneInfo)› -/
#guard_msgs in #reprint "`(· $h:hygieneInfo)"

/-!
The same for the other parsers that follow a token with `hygieneInfo`: `(` in `hygienicLParen`,
and `suffices`.
-/
/-- info: ‹`(( $h:hygieneInfo x))› -/
#guard_msgs in #reprint "`(( $h:hygieneInfo x))"

/-- info: ‹`(suffices $h:hygieneInfo p from q; r)› -/
#guard_msgs in #reprint "`(suffices $h:hygieneInfo p from q; r)"

/-!
Without an antiquotation `hygieneInfoFn` still runs, and reprinting is unaffected: the whitespace
only moves from `·` onto the `hygieneInfo` node.
-/
/-- info: ‹(· + 1)› -/
#guard_msgs in #reprint "(· + 1)"
