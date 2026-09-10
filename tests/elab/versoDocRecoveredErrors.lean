import Lean
open Lean Parser Elab.Command

/-!
Error recovery earlier in a declaration must not discard the errors that recovery reported, nor the
docstring that follows it. Both are lost when the check for a failed docstring parse consults the
errors that were already present before the docstring was parsed.
-/

/-- Parses `doc` as a command with Verso docstrings enabled, and reports what survived. -/
def parseWithVersoDocs (doc : String) : CommandElabM Unit := do
  let env ← getEnv
  let pmctx : ParserModuleContext :=
    { env, options := (← getOptions).setBool `doc.verso true,
      currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls }
  let ictx := mkInputContext doc "<test>"
  let p := andthenFn whitespace (categoryParserFnImpl `command)
  let s := p.run ictx pmctx (getTokenTable env) (mkParserState doc)
  let docstringLost := s.stxStack.toSubarray.toArray.any fun stx =>
    (stx.find? (·.isOfKind `Lean.Doc.Syntax.parseFailure)).isSome
  logInfo m!"recovered errors: {s.recoveredErrors.size}, docstring lost: {docstringLost}"

/-- info: recovered errors: 1, docstring lost: false -/
#guard_msgs in
#eval parseWithVersoDocs "inductive where\n  /-- A good docstring. -/\n  | c"

-- Without an earlier recovery the docstring is kept, as it always was.
/-- info: recovered errors: 0, docstring lost: false -/
#guard_msgs in
#eval parseWithVersoDocs "inductive I where\n  /-- A good docstring. -/\n  | c"

-- A docstring that really does fail to parse is still reported as a failure.
/-- info: recovered errors: 0, docstring lost: true -/
#guard_msgs in
#eval parseWithVersoDocs "inductive I where\n  /-- unclosed *emph -/\n  | c"
