import Lean.DocString.Links
import Lean.DocString
import Lean.Elab.Command

/-!
These tests ensure that links to documentation are correctly validated, and that they are correctly rewritten.
-/

set_option guard_msgs.diff true

open Lean Elab Command

/-!
# Check All Built-In Docstrings

Manual links in built-in docstrings aren't validated when adding them, so they are checked here.

This is an over-approximation: it checks all the docstrings in Lean.
-/

/-!
First, define one broken builtin docstring to make sure that the test actually catches them.
-/
def check := 5
#eval addBuiltinDocString `check "Here's a broken manual link: lean-manual://oops\n"

/-!
Now validate the docstrings.
-/

/--
error: Docstring errors for 'check': ⏎
   • "lean-manual://oops":
    Unknown documentation type `oops`. Expected one of the following: `section`, `errorExplanation`
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (x, _) in env.constants do
    if let some str ← findSimpleDocString? env x (includeBuiltin := true) then
      let (errs, _) ← rewriteManualLinksCore str
      if !errs.isEmpty then
        let errMsgs := errs.map fun (⟨s, e⟩, msg) => m!" • {repr <| str.extract s e}:{indentD msg}"
        logError <| m!"Docstring errors for '{x}': {indentD <| MessageData.joinSep errMsgs.toList "\n"}\n\n"


/-! # Test Link Rewriting -/

/--
Tests the result of the link rewriting procedure.

The result, along with any errors, are converted to readable info that can be captured in
`#guard_msgs`. Errors are associated with their substrings to check that the association is correct
as well. Finally, the actual manual URL is replaced with `MANUAL` in order to make the test robust
in the face of changes to the underlying default.
-/
def checkResult (str : String) : CommandElabM Unit := do
  let result ← rewriteManualLinksCore str

  if !result.1.isEmpty then
    let errMsgs := result.1.map fun (⟨s, e⟩, msg) => m!" • {repr <| str.extract s e}:{indentD msg}"
    logInfo <| m!"Errors: {indentD <| MessageData.joinSep errMsgs.toList "\n"}\n\n"

  let root := manualRoot
  logInfo m!"Result: {repr <| result.2.replace root "MANUAL/"}"


/-- info: Result: "abc" -/
#guard_msgs in
#eval checkResult "abc"

/-- info: Result: "abc []()" -/
#guard_msgs in
#eval checkResult "abc []()"

/-- info: Result: "abc [](MANUAL/find/?domain=Verso.Genre.Manual.section&name=the-section-id)" -/
#guard_msgs in
#eval checkResult "abc [](lean-manual://section/the-section-id)"

/-- info: Result: "abc [](MANUAL/find/?domain=Manual.errorExplanation&name=lean.myErrorName)" -/
#guard_msgs in
#eval checkResult "abc [](lean-manual://errorExplanation/lean.myErrorName)"

/--
info: Result: "abc\n\nMANUAL/find/?domain=Verso.Genre.Manual.section&name=the-section-id\n\nmore text"
-/
#guard_msgs in
#eval checkResult
  "abc

lean-manual://section/the-section-id

more text"

/--
info: Result: "abc\n\nMANUAL/find/?domain=Verso.Genre.Manual.section&name=the-section-id\n\nmore text\n"
-/
#guard_msgs in
#eval checkResult
  "abc

lean-manual://section/the-section-id

more text
"


/--
info: Errors: ⏎
   • "lean-manual://":
    Missing documentation type
   • "lean-manual://f":
    Unknown documentation type `f`. Expected one of the following: `section`, `errorExplanation`
   • "lean-manual://a/":
    Unknown documentation type `a`. Expected one of the following: `section`, `errorExplanation`

---
info: Result: "foo [](lean-manual://) [](lean-manual://f) lean-manual://a/b"
-/
#guard_msgs in
#eval checkResult "foo [](lean-manual://) [](lean-manual://f) lean-manual://a/b"

/--
info: Errors: ⏎
   • "lean-manual://":
    Missing documentation type
   • "lean-manual://f":
    Unknown documentation type `f`. Expected one of the following: `section`, `errorExplanation`
   • "lean-manual://a/b":
    Unknown documentation type `a`. Expected one of the following: `section`, `errorExplanation`

---
info: Result: "foo [](lean-manual://) [](lean-manual://f) lean-manual://a/b "
-/
#guard_msgs in
#eval checkResult "foo [](lean-manual://) [](lean-manual://f) lean-manual://a/b "


/-- info: Result: "abc [](https://foo)" -/
#guard_msgs in
#eval checkResult "abc [](https://foo)"

/--
info: Errors: ⏎
   • "lean-manual://":
    Missing documentation type

---
info: Result: "a b c\nlean-manual://\n"
-/
#guard_msgs in
#eval checkResult "a b c\nlean-manual://\n"


/--
error: Missing documentation type
---
error: Unknown documentation type `f`. Expected one of the following: `section`, `errorExplanation`
-/
#guard_msgs in
/--
foo [](lean-manual://) [](lean-manual://f)
-/
def x := 44

/-!
# Environment Variable Tests

These tests check that the `LEAN_MANUAL_ROOT` environment variable affects rewriting as expected.
-/

def checkResultWithRoot (root : Option String) (str : String) : IO Unit := do
  let lean ← IO.appPath
  IO.FS.withTempFile fun h path => do
    h.putStrLn r###"
import Lean.DocString.Links

open Lean

def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut str := ""
  let mut l ← stdin.getLine
  while !l.isEmpty do
    str := str ++ l
    l ← stdin.getLine
  IO.println (repr (← rewriteManualLinksCore str))
"###
    h.flush
    let child ← IO.Process.spawn {
      cmd := lean.toString,
      args := #["--run", path.toString],
      env := #[("LEAN_MANUAL_ROOT", root)],
      stdout := .piped, stderr := .piped, stdin := .piped
    }
    let child ← do
      let (stdin, child) ← child.takeStdin
      stdin.putStrLn str
      pure child
    let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    let stdout ← IO.ofExcept stdout.get


    IO.println s!"Exit code: {exitCode}"
    IO.println "Stdout:"
    IO.println stdout
    IO.println "Stderr:"
    IO.println stderr

/--
info: Exit code: 0
Stdout:
(#[], "\n")

Stderr:
-/
#guard_msgs in
#eval checkResultWithRoot "OVERRIDDEN_ROOT" ""

/--
info: Exit code: 0
Stdout:
(#[], "OVERRIDDEN_ROOT/find/?domain=Verso.Genre.Manual.section&name=foo\n")

Stderr:
-/
#guard_msgs in
#eval checkResultWithRoot "OVERRIDDEN_ROOT" "lean-manual://section/foo"

/--
info: Exit code: 0
Stdout:
(#[], "OVERRIDDEN_ROOT/find/?domain=Verso.Genre.Manual.section&name=foo\n")

Stderr:
-/
#guard_msgs in
#eval checkResultWithRoot "OVERRIDDEN_ROOT/" "lean-manual://section/foo"


/--
info: Exit code: 0
Stdout:
(#[({ start := { byteIdx := 0 }, stop := { byteIdx := 22 } }, "Empty section ID")], "lean-manual://section/\n")

Stderr:
-/
#guard_msgs in
#eval checkResultWithRoot "OVERRIDDEN_ROOT" "lean-manual://section/"

/--
info: Exit code: 0
Stdout:
(#[({ start := { byteIdx := 0 }, stop := { byteIdx := 21 } }, "Expected one item after `section`, but got []")],
 "lean-manual://section\n")

Stderr:
-/
#guard_msgs in
#eval checkResultWithRoot "OVERRIDDEN_ROOT" "lean-manual://section"

/--
info: Exit code: 0
Stdout:
(#[({ start := { byteIdx := 0 }, stop := { byteIdx := 15 } },
    "Unknown documentation type `s`. Expected one of the following: `section`, `errorExplanation`")],
 "lean-manual://s\n")

Stderr:
-/
#guard_msgs in
#eval checkResultWithRoot "OVERRIDDEN_ROOT" "lean-manual://s"

/-!
# Syntax Errors in Manual Links

Should an unvalidated docstring sneak into the environment, syntax errors in its Lean manual links
are reported in the docstring.
-/

def bogus := "bogus"

#eval Lean.addDocStringCore ``bogus
  r#"See [the manual](lean-manual://invalid/link)

It contains many things of lean-manual:// interest

It contains many further things of even greater lean-manual://section/ interest

It contains many further things of even greater lean-manual://section/aaaaa/bbbb interest
"#

/--
info: See [the manual](lean-manual://invalid/link)

It contains many things of lean-manual:// interest

It contains many further things of even greater lean-manual://section/ interest

It contains many further things of even greater lean-manual://section/aaaaa/bbbb interest


**❌ Syntax Errors in Lean Language Reference Links**

The `lean-manual` URL scheme is used to link to the version of the Lean reference manual that
corresponds to this version of Lean. Errors occurred while processing the links in this documentation
comment:
 * ```lean-manual://invalid/link```: Unknown documentation type `invalid`. Expected one of the following: `section`, `errorExplanation`

 * ```lean-manual://```: Missing documentation type

 * ```lean-manual://section/```: Empty section ID

 * ```lean-manual://section/aaaaa/bbbb```: Expected one item after `section`, but got [aaaaa, bbbb]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let str ← Lean.findDocString? (← getEnv) ``bogus
  str.forM (logInfo ·)
