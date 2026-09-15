module
import Lean

/-!
Test parsing, pretty printing, and quotation splices for the shared `grindParam` category (#15116).
The category must retain the syntax trees used by `grind`, `lia`, and `grobner`.
-/

open Lean Elab Command

private meta def checkRoundTrip (cat : Name) (input : String) : CoreM Syntax := do
  let env ← getEnv
  let stx ← ofExcept <| Parser.runParserCategory env cat input
  let formatted := (← PrettyPrinter.ppCategory cat stx).pretty
  let reparsed ← ofExcept <| Parser.runParserCategory env cat formatted
  unless stx == reparsed do
    throwError "syntax did not round-trip: {input} → {formatted}"
  return stx

run_cmd liftTermElabM do
  let cat := `Lean.Parser.Tactic.grindParam
  for input in #["foo", "foo x", "= foo", "! foo", "! = foo", "- foo", "#abcd",
      "gen foo", "→ foo", "← foo", "usr foo", "(show True from trivial)"] do
    let stx ← checkRoundTrip cat input
    unless stx.getKind == cat && stx.getNumArgs == 1 do
      throwError "unexpected parameter syntax: {stx}"
    for tacName in #["grind", "grind?", "lia", "grobner"] do
      discard <| checkRoundTrip `tactic s!"{tacName} [{input}]"
    discard <| checkRoundTrip `tactic s!"sym [{input}] => skip"
    for tacName in #["finish", "finish?"] do
      discard <| checkRoundTrip `grind s!"{tacName} [{input}]"

macro "lia_with " ps:Lean.Parser.Tactic.grindParam,* : tactic =>
  `(tactic| lia [$ps,*])

macro "grind_with " p:Lean.Parser.Tactic.grindParam : tactic => do
  let `(Lean.Parser.Tactic.grindParam| = $e:term) := p
    | Macro.throwUnsupported
  let p ← `(Lean.Parser.Tactic.grindParam| = $e:term)
  `(tactic| grind only [$p:grindParam])

private def bump (x : Int) := x + 1
private theorem bump_def (x : Int) : bump x = x + 1 := rfl

example (x : Int) : x < bump x := by lia_with bump_def x
example (x : Int) : x < bump x := by lia_with = bump_def
example (x : Int) : x < bump x := by grind_with = bump_def

example (x : Int) : x < bump x := by
  grind => finish [= bump_def]
