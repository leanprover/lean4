module
import Lean

/-!
Test shared modifier parsing for `grind` attributes and tactic parameters (#15116).
Preserve syntax trees, pretty printing, and existing typed and anonymous quotation splices.
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
  for input in #["foo", "foo x", "= foo", "! foo", "! = foo", "- foo", "#abcd",
      "gen foo", "→ foo", "← foo", "usr foo", "(show True from trivial)"] do
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

macro "lia_modified " mod:Lean.Parser.Attr.grindMod e:term : tactic => do
  let p ← `(Lean.Parser.Tactic.grindParam| $mod $e:term)
  `(tactic| lia [$p:grindParam])

example (x : Int) : x < bump x := by lia_modified = bump_def

run_cmd liftTermElabM do
  for modifier in #["=", "= gen", "=_", "=_ gen", "_=_", "_=_ gen", "←=", "<-=",
      "←", "<-", "← gen", "→", "->", "⇐", "<=", "⇒", "=>", ".", "·", ". gen",
      "usr", "cases", "cases eager", "intro", "ext", "gen", "symbol 0", "symbol low",
      "inj", "funCC", "hom_pred", "hom", "norm", "norm ↓", "norm ↑", "norm ←", "norm <-",
      "unfold"] do
    discard <| checkRoundTrip `attr s!"grind {modifier}"
    discard <| checkRoundTrip `tactic s!"grind [{modifier} foo]"
    discard <| checkRoundTrip `tactic s!"grind [! {modifier} foo]"

open Parser.Attr

syntax "mod_choice" grind_mod "category" : tactic
syntax "mod_choice" grindMod "named" : tactic
syntax "mod_category" grind_mod : tactic
syntax "mod_named" grindMod : tactic

private meta partial def antiquotKinds (s : Syntax) : Array Name :=
  s.getArgs.foldl (fun ns s => ns ++ antiquotKinds s)
    (if s.isAntiquot then #[s.getKind] else #[])

-- Backtracking must preserve the distinct antiquotation kinds of categories and named parsers.
run_cmd do
  for (input, expected) in #[
      ("mod_category $x", `grind_mod.pseudo.antiquot),
      ("mod_named $x", `Lean.Parser.Attr.grindMod.antiquot),
      ("mod_choice $x category", `grind_mod.pseudo.antiquot),
      ("mod_choice $x named", `Lean.Parser.Attr.grindMod.antiquot)] do
    let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term s!"`(tactic| {input})"
    unless antiquotKinds stx == #[expected] do
      throwError "unexpected antiquotation kinds for {input}: {antiquotKinds stx}"
