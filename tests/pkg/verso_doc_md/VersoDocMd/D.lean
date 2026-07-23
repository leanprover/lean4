module

public meta import Lean
public meta import VersoDocMd.Defs
import all VersoDocMd.A

open Lean Doc Elab Command
open scoped Lean.Doc.Syntax

public section

/-!
A second include role that resolves the target eagerly: it reads the docstring straight from the
environment as the role elaborates, splicing the text in, rather than deferring to a Markdown
renderer. `A` is imported with `all`, so `Foo`'s server-level docstring is reachable from the
environment lookup without `Elab.inServer`.
-/

/-- Includes another declaration's docstring by reading it from the environment as the role
elaborates. -/
@[doc_role]
meta def include_docstring' (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let target ← codeTargetName xs
  match (← (findInternalDocString? (← getEnv) target : IO _)) with
  | some (.inl str) => return .text str
  | _ => return .concat #[]

set_option doc.verso true
set_option doc.verso.suggestions false

/-- Including: {include_docstring'}`Foo` -/
def Baz : Nat := 2

/-- info: Including: Hello from Foo across modules. -/
#guard_msgs in
run_meta do
  let env ← getEnv
  let some r ← findDocString? env `Baz | failure
  let expected := "Including: Hello from Foo across modules."
  unless r.startsWith expected do throwError m!"unexpected render: {repr r}"
  logInfo expected
